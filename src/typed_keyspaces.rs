use std::{
    fmt::{self, Debug},
    hash::BuildHasher,
    marker::PhantomData,
    mem,
    ops::RangeBounds,
    sync::{Arc, atomic::AtomicU64},
};

use byteview::ByteView;
use fjall::{Keyspace, Slice};

use quick_cache::{UnitWeighter, sync::Cache};
use rkyv::{
    Archive, Serialize,
    api::high::{HighSerializer, to_bytes_in},
    rancor::Source,
    ser::allocator::ArenaHandle,
};

use crate::rkyved::{BuilderWriter, PhantomAllAutoTraits, PortableView, PortableViewCanValidate};

pub type ArchivedView<T> = PortableView<<T as Archive>::Archived, fjall::Slice>;

pub struct TypedKeyspace<K, V, const KEY_SIZE: usize = 8>
where
    V: Archive,
{
    _tys: PhantomAllAutoTraits<(K, V)>,
    cache: Arc<Cache<[u8; KEY_SIZE], ArchivedView<V>>>,
    tree: Keyspace,
}

#[derive(Debug)]
pub struct InvalidIndexError;
impl fmt::Display for InvalidIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid db index detected in tree")
    }
}

impl std::error::Error for InvalidIndexError {}

#[must_use]
pub struct Commit<V: Archive, const KEY_SIZE: usize = 8> {
    key: [u8; KEY_SIZE],
    value: ArchivedView<V>,
}

impl<K, V, const N: usize> TypedKeyspace<K, V, N>
where
    K: Into<[u8; N]> + From<[u8; N]> + Copy,
    V: Archive,
{
    pub fn new(tree: Keyspace, cache_cap: usize) -> Self {
        Self {
            cache: Cache::new(cache_cap).into(),
            tree,
            _tys: PhantomData,
        }
    }
    pub fn get<E>(&self, key: K) -> Result<Option<ArchivedView<V>>, E>
    where
        E: Source,
        V::Archived: PortableViewCanValidate<E>,
    {
        let key = key.into();

        match self.cache.get_or_insert_with(&key, || {
            self.tree
                .get(key)
                .map_err(|v| Some(E::new(v)))
                .and_then(|v| {
                    PortableView::<V::Archived, _>::new::<E>(v.ok_or(None)?).map_err(Some)
                })
        }) {
            Ok(v) => Ok(Some(v)),
            Err(e) => match e {
                None => Ok(None),
                Some(e) => Err(e),
            },
        }
    }
    pub fn iter<E>(&self) -> impl DoubleEndedIterator<Item = Result<ArchivedView<V>, E>>
    where
        V::Archived: PortableViewCanValidate<E>,
        E: Source,
    {
        let cache = self.cache.clone();
        self.tree.iter().map(move |v| {
            let (k, v) = v.into_inner().map_err(E::new)?;

            cache.get_or_insert_with(k.first_chunk().unwrap(), || {
                PortableView::<V::Archived, Slice>::new(v)
            })
        })
    }
    pub fn iter_prefix<E, const P: usize>(
        &self,
        prefix: [u8; P],
    ) -> impl DoubleEndedIterator<Item = Result<(K, ArchivedView<V>), E>>
    where
        V::Archived: PortableViewCanValidate<E>,
        E: Source,
    {
        let cache = self.cache.clone();
        self.tree.prefix(prefix).map(move |v| {
            let (k, v) = v.into_inner().map_err(E::new)?;
            let kbs = k.first_chunk().unwrap();
            Ok((
                (*kbs).into(),
                cache.get_or_insert_with(kbs, || PortableView::<V::Archived, Slice>::new(v))?,
            ))
        })
    }
    pub fn iter_range<'a, E, const P: usize>(
        &'a self,
        range: impl RangeBounds<[u8; P]> + 'a,
    ) -> impl DoubleEndedIterator<Item = Result<(K, ArchivedView<V>), E>>
    where
        V::Archived: PortableViewCanValidate<E>,
        E: Source,
    {
        let cache = self.cache.clone();
        self.tree.range(range).map(move |v| {
            let (k, v) = v.into_inner().map_err(E::new)?;
            let kbs = k.first_chunk().unwrap();
            Ok((
                (*kbs).into(),
                cache.get_or_insert_with(kbs, || PortableView::<V::Archived, Slice>::new(v))?,
            ))
        })
    }
    pub fn insert_batched<E>(
        &self,
        batch_fn: &mut impl FnMut(&Keyspace, ByteView, ByteView) -> Result<(), E>,
        key: K,
        val: V,
    ) -> Result<Commit<V, N>, E>
    where
        V: for<'a> Serialize<HighSerializer<BuilderWriter, ArenaHandle<'a>, E>>,
        E: Source,
    {
        let key = key.into();
        let ser = to_bytes_in(&val, BuilderWriter::new(mem::size_of::<V::Archived>()))?.finish();
        let c = Commit {
            key,
            // Safety: we just serialized this value
            value: unsafe { PortableView::new_unchecked(ser.clone().into()) },
        };
        batch_fn(&self.tree, key.into(), ser)?;
        Ok(c)
    }
    pub fn commit(&self, c: Commit<V, N>) {
        let Commit { key, value } = c;
        self.cache.insert(key, value);
    }
    pub fn insert<E>(&self, key: K, val: V) -> Result<(), E>
    where
        V: for<'a> Serialize<HighSerializer<BuilderWriter, ArenaHandle<'a>, E>>,
        E: Source,
    {
        self.commit(self.insert_batched(
            &mut |tree, k, v| tree.insert(k, v).map_err(E::new),
            key,
            val,
        )?);
        Ok(())
    }
}

/// Interns a (potentially large) canonical identity to a much more compact locally unique integer id for more efficient usage elsewhere. Keys must be larger than one byte
pub struct IdentityKeyspace<K, V: From<u64>, H = ahash::RandomState> {
    tree: Keyspace,
    cache: Cache<ByteView, u64, UnitWeighter, H>,
    next: AtomicU64,
    _boo: PhantomAllAutoTraits<(K, V)>,
}

#[must_use]
pub struct ICommit<V> {
    key: Option<ByteView>,
    val: u64,
    _boo: PhantomAllAutoTraits<V>,
}
impl<V> ICommit<V>
where
    u64: Into<V>,
{
    pub fn val(&self) -> V {
        self.val.into()
    }
}
const BLESSED_COUNTER: [u8; 1] = [0];
impl<K: AsRef<[u8]>, V: From<u64>, H: BuildHasher + Default + Clone> IdentityKeyspace<K, V, H> {
    pub fn read_counter<E>(k: &Keyspace) -> Result<u64, E>
    where
        E: Source,
    {
        // a little evil
        Ok(if let Some(v) = k.get(BLESSED_COUNTER).map_err(E::new)? {
            u64::from_le_bytes(
                *v.first_chunk::<8>()
                    .expect("8 bytes to be present in counter value"),
            )
        } else {
            0
        })
    }
    // require exclusive access as a lint to avoid racing on the counter value, which will break our logical invariants.
    // the reason this can't be written by a batch is that batches may be applied out of order,
    // so an old batch could overwrite the counter value for a new one.
    pub fn save_ctr<E>(&mut self) -> Result<(), E>
    where
        E: Source,
    {
        self.tree
            .insert(
                BLESSED_COUNTER,
                self.next
                    .load(std::sync::atomic::Ordering::SeqCst)
                    .to_le_bytes(),
            )
            .map_err(E::new)
    }
    pub fn new<E>(tree: Keyspace, cache_cap: usize) -> Result<Self, E>
    where
        E: Source,
    {
        Ok(Self {
            next: AtomicU64::new(Self::read_counter(&tree)?),
            tree,

            cache: Cache::with(
                cache_cap,
                cache_cap as u64,
                Default::default(),
                H::default(),
                Default::default(),
            ),
            _boo: PhantomData,
        })
    }
    pub fn reserve(&self) -> u64 {
        // guarantee key uniqueness. May cause gaps for write batches which are
        // never committed but that's an exceedly unlikely occurrence
        self.next.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    pub fn get_or_insert_batched<E>(
        &self,
        write_batch: &mut impl FnMut(&Keyspace, ByteView, ByteView) -> Result<(), E>,
        val: K,
    ) -> Result<ICommit<V>, E>
    where
        E: Source,
    {
        let key_bytes = val.as_ref();
        assert!(key_bytes.len() > 1);
        let key_view = ByteView::new(key_bytes);
        match self.cache.get(&key_view) {
            Some(cached) => Ok(ICommit {
                key: None,
                val: cached,
                _boo: PhantomData,
            }),
            None => {
                if let Some(existing) = self.tree.get(key_bytes).map_err(E::new)? {
                    Ok(ICommit {
                        key: None,
                        val: u64::from_le_bytes(
                            *existing
                                .first_chunk::<8>()
                                .expect("8 bytes to be present in interned id"),
                        ),
                        _boo: PhantomData,
                    })
                } else {
                    let nkey = self.reserve();
                    let b = nkey.to_le_bytes();
                    write_batch(&self.tree, key_view.clone(), b.into())?;
                    Ok(ICommit {
                        key: Some(key_view),
                        val: nkey,
                        _boo: PhantomData,
                    })
                }
            }
        }
    }
    pub fn commit(&self, c: ICommit<V>) -> V {
        if let Some(k) = c.key {
            self.cache.insert(k, c.val);
        }
        c.val.into()
    }
    pub fn get_or_insert<E>(&self, val: K) -> Result<V, E>
    where
        E: Source,
    {
        Ok(self.commit(
            self.get_or_insert_batched(&mut |t, k, v| t.insert(k, v).map_err(E::new), val)?,
        ))
    }
    pub fn iter<E>(&self) -> impl DoubleEndedIterator<Item = Result<V, E>>
    where
        E: Source,
    {
        self.tree
            .iter()
            .filter_map(|v| match v.into_inner().map_err(E::new) {
                Ok((k, v)) => {
                    if k.len() != 1 {
                        Some(Ok(V::from(u64::from_le_bytes(
                            *v.first_chunk().expect("8 bytes in identityintern value"),
                        ))))
                    } else {
                        None
                    }
                }
                Err(e) => Some(Err(e)),
            })
    }
}
impl<K, V: From<u64>, H> Drop for IdentityKeyspace<K, V, H> {
    fn drop(&mut self) {
        self.tree
            .insert(
                BLESSED_COUNTER,
                self.next
                    .load(std::sync::atomic::Ordering::SeqCst)
                    .to_le_bytes(),
            )
            .expect("write of counter to succeed");
    }
}
