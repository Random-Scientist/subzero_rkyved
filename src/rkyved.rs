use byteview::ByteView;
use std::{
    cell::RefCell,
    fmt::Debug,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use rkyv::{
    Archive, Deserialize, Portable,
    api::{check_pos_with_context, high::HighDeserializer, root_position},
    bytecheck::CheckBytes,
    rancor::Source,
    seal::Seal,
    ser::{Positional, Writer},
    traits::NoUndef,
    util::AlignedVec,
    validation::{Validator, archive::ArchiveValidator},
};

pub type PhantomAllAutoTraits<T> = std::marker::PhantomData<fn(T) -> T>;

/// # Safety
/// Implementors must ensure that calling [`AsRef::as_ref`] or [`AsMut::as_mut`] on a value of this type has
/// no side effects on the state of the returned buffer
pub unsafe trait StableBytes {}

// Safety: <&'_ T as AsMut>::as_mut nor <&'_ T as AsRef>::as_ref modify T
unsafe impl StableBytes for &'_ [u8] {}
// Safety: <&'_ mut T as AsMut>::as_mut nor <&'_ mut T as AsRef>::as_ref modify T
unsafe impl StableBytes for &'_ mut [u8] {}
// Safety: <fjall::Slice as AsMut>::as_mut nor <fjall::Slice as AsRef>::as_ref modify the buffer held by the IVec
unsafe impl StableBytes for fjall::Slice {}
// Safety: <AlignedVec<_> as AsMut>::as_mut nor <AlignedVec<_> as AsRef>::as_ref modify the buffer held by the IVec
unsafe impl<const A: usize> StableBytes for AlignedVec<A> {}

pub struct BuilderWriter(usize, byteview::Builder);

impl BuilderWriter {
    pub fn new(cap: usize) -> Self {
        // Safety: we promise not to read from indices we haven't initialized yet
        Self(0, unsafe { ByteView::builder_unzeroed(cap) })
    }
    pub fn finish(self) -> ByteView {
        let view = self.1.freeze();
        // slice down to uninit range
        let r = view.slice(0..self.0);
        // discard unsound, possibly partially uninit buf
        drop(view);
        r
    }
}

impl Positional for BuilderWriter {
    fn pos(&self) -> usize {
        self.0
    }
}

impl<E> Writer<E> for BuilderWriter
where
    E: Source,
{
    fn write(&mut self, bytes: &[u8]) -> Result<(), E> {
        let cap = self.1.len();
        let free = cap - self.0;

        let blen = bytes.len();
        let npos = self.0 + blen;
        if free < blen {
            //realloc
            let new_req = (cap * 2).max(cap + blen);
            // Safety: we promise not to read from indices we haven't initialized yet
            let mut b = unsafe { ByteView::builder_unzeroed(new_req) };

            b[0..self.0].copy_from_slice(&self.1[0..self.0]);
            // plus incoming
            b[self.0..self.0 + blen].copy_from_slice(bytes);

            self.1 = b;
        } else {
            self.1[self.0..npos].copy_from_slice(bytes);
        }
        self.0 = npos;
        Ok(())
    }
}

/// Prechecked view of an [`rkyv`]ed type in a byte buffer
pub struct PortableView<T: ?Sized, Buf> {
    backing: Buf,
    ty: PhantomAllAutoTraits<T>,
}

#[derive(Clone, Copy)]
pub struct ProjectRef<F, T: ?Sized, Buf> {
    backing: PortableView<T, Buf>,
    project: F,
}

impl<F: Fn(&T) -> &U + Clone + 'static, U: ?Sized, T: ?Sized, Buf> ProjectRef<F, T, Buf>
where
    PortableView<T, Buf>: Clone + Deref<Target = T>,
{
    pub fn project<V>(
        &self,
        project: impl for<'a> Fn(&'a U) -> &'a V + 'static,
    ) -> ProjectRef<impl Fn(&T) -> &V, T, Buf>
    where
        U: 'static,
        V: ?Sized,
    {
        fn compose<InnerT, CurrT, NextT, InnerFn, OuterFn>(
            inner: InnerFn,
            outer: OuterFn,
        ) -> impl Fn(&InnerT) -> &NextT
        where
            InnerFn: (Fn(&InnerT) -> &CurrT) + 'static,
            OuterFn: (Fn(&CurrT) -> &NextT) + 'static,
            InnerT: ?Sized,
            CurrT: ?Sized + 'static,
            NextT: ?Sized,
        {
            #[inline]
            move |r| outer(inner(r))
        }
        ProjectRef {
            project: compose(self.project.clone(), project),
            backing: self.backing.clone(),
        }
    }
}

impl<F, U: ?Sized, T, Buf> Deref for ProjectRef<F, T, Buf>
where
    PortableView<T, Buf>: Deref<Target = T>,
    F: Fn(&T) -> &U,
{
    type Target = U;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}
impl<F, U: ?Sized, T, Buf> AsRef<U> for ProjectRef<F, T, Buf>
where
    PortableView<T, Buf>: Deref<Target = T>,
    F: Fn(&T) -> &U,
{
    fn as_ref(&self) -> &U {
        (self.project)(&*self.backing)
    }
}

impl<T, Buf> Clone for PortableView<T, Buf>
where
    Buf: Clone,
{
    fn clone(&self) -> Self {
        Self {
            backing: self.backing.clone(),
            ty: PhantomData,
        }
    }
}

impl<T, Buf> Copy for PortableView<T, Buf> where Buf: Copy {}

impl<T, Buf> Debug for PortableView<T, Buf>
where
    T: Portable + Debug,
    Buf: StableBytes + AsRef<[u8]>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ArchivedView").field(self.get()).finish()
    }
}
// duplicated from rkyv to make `fn new` const
mod validator_const_init {
    use core::{any::TypeId, error::Error, fmt, hash::BuildHasherDefault};
    use std::collections::{HashMap, hash_map};

    use rancor::{Source, Strategy, fail};

    use rkyv::{
        hash::FxHasher64,
        validation::{
            SharedContext, Validator, archive::ArchiveValidator, shared::ValidationState,
        },
    };
    pub(super) type ConstInitHighValidator<'a, 's, E> =
        Strategy<Validator<ArchiveValidator<'a>, &'s mut ConstInitSharedValidator>, E>;
    /// A validator that can verify shared pointers.
    #[derive(Debug, Default)]
    pub struct ConstInitSharedValidator {
        shared: hash_map::HashMap<usize, (TypeId, bool), BuildHasherDefault<FxHasher64>>,
    }

    impl ConstInitSharedValidator {
        /// Creates a new shared pointer validator.
        #[inline]
        pub const fn new() -> Self {
            Self {
                shared: HashMap::with_hasher(BuildHasherDefault::new()),
            }
        }

        /// Creates a new shared pointer validator with specific capacity.
        #[inline]
        pub fn with_capacity(capacity: usize) -> Self {
            Self {
                shared: hash_map::HashMap::with_capacity_and_hasher(capacity, Default::default()),
            }
        }
        pub fn reset(&mut self) {
            self.shared.clear();
        }
    }

    #[derive(Debug)]
    struct TypeMismatch {
        previous: TypeId,
        current: TypeId,
    }

    impl fmt::Display for TypeMismatch {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "the same memory region has been claimed as two different types: \
             {:?} and {:?}",
                self.previous, self.current,
            )
        }
    }

    impl Error for TypeMismatch {}

    #[derive(Debug)]
    struct NotStarted;

    impl fmt::Display for NotStarted {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "shared pointer was not started validation")
        }
    }

    impl Error for NotStarted {}

    #[derive(Debug)]
    struct AlreadyFinished;

    impl fmt::Display for AlreadyFinished {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "shared pointer was already finished validation")
        }
    }

    impl Error for AlreadyFinished {}

    impl<E: Source> SharedContext<E> for &'_ mut ConstInitSharedValidator {
        fn start_shared(&mut self, address: usize, type_id: TypeId) -> Result<ValidationState, E> {
            match self.shared.entry(address) {
                hash_map::Entry::Vacant(vacant) => {
                    vacant.insert((type_id, false));
                    Ok(ValidationState::Started)
                }
                hash_map::Entry::Occupied(occupied) => {
                    let (previous_type_id, finished) = occupied.get();
                    if previous_type_id != &type_id {
                        fail!(TypeMismatch {
                            previous: *previous_type_id,
                            current: type_id,
                        })
                    } else if !finished {
                        Ok(ValidationState::Pending)
                    } else {
                        Ok(ValidationState::Finished)
                    }
                }
            }
        }

        fn finish_shared(&mut self, address: usize, type_id: TypeId) -> Result<(), E> {
            match self.shared.entry(address) {
                hash_map::Entry::Vacant(_) => fail!(NotStarted),
                hash_map::Entry::Occupied(mut occupied) => {
                    let (previous_type_id, finished) = occupied.get_mut();
                    if previous_type_id != &type_id {
                        fail!(TypeMismatch {
                            previous: *previous_type_id,
                            current: type_id,
                        });
                    } else if *finished {
                        fail!(AlreadyFinished);
                    } else {
                        *finished = true;
                        Ok(())
                    }
                }
            }
        }
    }
}
pub trait PortableViewCanValidate<E>:
    for<'a, 's> CheckBytes<validator_const_init::ConstInitHighValidator<'a, 's, E>>
{
}
impl<T, E: Source> PortableViewCanValidate<E> for T where
    T: for<'a, 's> CheckBytes<validator_const_init::ConstInitHighValidator<'a, 's, E>>
{
}
thread_local! {
    static VALIDATOR: RefCell<validator_const_init::ConstInitSharedValidator> = const { RefCell::new(validator_const_init::ConstInitSharedValidator::new()) };
}
impl<T, Buf> PortableView<T, Buf>
where
    T: Portable,
    Buf: StableBytes,
{
    /// # Safety
    /// Buf must contain a serialized byte representation that upholds all validity invariants of [`rkyv::access_unchecked<T>`]
    pub unsafe fn new_unchecked(buf: Buf) -> Self {
        Self {
            backing: buf,
            ty: PhantomData,
        }
    }
    pub fn new<E>(buf: Buf) -> Result<Self, E>
    where
        T: PortableViewCanValidate<E>,
        Buf: AsRef<[u8]>,
        E: Source,
    {
        // partial reimplementation of `rkyv::access`
        let r = buf.as_ref();
        let root_pos = root_position::<T>(r.len());

        // stow the allocating SharedValidator (internal HashMap) in a thread local to amortize its allocation.
        // won't ever panic because the body of the closure can't reach back to `VALIDATOR.with` (which is private to this module) again.
        VALIDATOR.with(|cell| {
            let shared = &mut *cell.borrow_mut();
            shared.reset();
            let mut validator = Validator::new(ArchiveValidator::new(r), shared);
            check_pos_with_context::<T, _, _>(r, root_pos, &mut validator)
        })?;

        Ok(Self {
            backing: buf,
            ty: PhantomData,
        })
    }
    #[inline]
    pub fn get(&self) -> &T
    where
        Buf: AsRef<[u8]>,
    {
        // Safety: by construction; this type may only be constructed for buffers that contain a valid instance of T according to `rkyv`
        // further, the only way that buffer is allowed to change is via mutations to T, which must maintain the validity of T
        unsafe { rkyv::access_unchecked(self.backing.as_ref()) }
    }
    #[inline]
    pub fn get_mut(&'_ mut self) -> Seal<'_, T>
    where
        Buf: AsMut<[u8]>,
    {
        // Safety: by construction; this type may only be constructed for buffers that contain a valid instance of T according to `rkyv`
        // further, the only way that buffer is allowed to change is via mutations to T, which must maintain the validity of T
        unsafe { rkyv::access_unchecked_mut(self.backing.as_mut()) }
    }
    pub fn project<U: ?Sized, F: Fn(&T) -> &U>(&self, project: F) -> ProjectRef<F, T, Buf>
    where
        Self: Clone,
    {
        ProjectRef {
            backing: self.clone(),
            project,
        }
    }
}

impl<T, Buf> Deref for PortableView<T, Buf>
where
    T: Portable,
    Buf: StableBytes + AsRef<[u8]>,
{
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

impl<T, Buf> DerefMut for PortableView<T, Buf>
where
    T: Portable + NoUndef + Unpin,
    // Need AsRef to guarantee the underlying Deref impl
    Buf: StableBytes + AsMut<[u8]> + AsRef<[u8]>,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.get_mut().unseal()
    }
}

#[derive(Clone)]
pub enum MaybeArchived<T, Buf>
where
    T: Archive,
{
    View(PortableView<T::Archived, Buf>),
    Val(T),
}

#[derive(Debug)]
pub enum MaybeArchivedRef<'a, T>
where
    T: Archive,
{
    View(&'a T::Archived),
    Val(&'a T),
}

impl<V> Copy for MaybeArchivedRef<'_, V> where V: Archive {}
impl<V> Clone for MaybeArchivedRef<'_, V>
where
    V: Archive,
{
    fn clone(&self) -> Self {
        *self
    }
}
pub trait InfallibleDeserializeExt: Portable {
    #[inline]
    fn deserialize<Dest>(&self) -> Dest
    where
        Self: Portable
            + Deserialize<Dest, HighDeserializer<rancor::Failure>>
            + Sized
            + FallibleDeserializeExt,
    {
        self.try_deserialize::<Dest, rancor::Failure>().unwrap()
    }
}

pub trait FallibleDeserializeExt: Portable {
    #[inline]
    fn try_deserialize<Dest, E>(&self) -> Result<Dest, E>
    where
        Self: Portable + Deserialize<Dest, HighDeserializer<E>> + Sized,
        E: Source,
    {
        rkyv::deserialize(self)
    }
}
impl<T: Portable> FallibleDeserializeExt for T {}
impl<T: Portable> InfallibleDeserializeExt for T {}

pub enum MaybeArchivedRefMut<'a, T: Archive> {
    View(Seal<'a, T::Archived>),
    Val(&'a mut T),
}

impl<T, Buf> MaybeArchived<T, Buf>
where
    T: Archive,
    Buf: AsRef<[u8]> + StableBytes,
{
    pub fn get<E>(self) -> Result<T, E>
    where
        E: Source,
        T::Archived: Deserialize<T, HighDeserializer<E>>,
        T: Clone,
    {
        match self {
            MaybeArchived::View(archived_view) => {
                let archived = &*archived_view;
                rkyv::deserialize(archived)
            }
            MaybeArchived::Val(val) => Ok(val),
        }
    }
    pub fn as_ref(&'_ self) -> MaybeArchivedRef<'_, T> {
        match self {
            MaybeArchived::View(archived_view) => MaybeArchivedRef::View(&**archived_view),
            MaybeArchived::Val(v) => MaybeArchivedRef::Val(v),
        }
    }
    pub fn as_mut(&'_ mut self) -> MaybeArchivedRefMut<'_, T>
    where
        Buf: AsMut<[u8]>,
    {
        match self {
            MaybeArchived::View(archived_view) => {
                MaybeArchivedRefMut::View(archived_view.get_mut())
            }
            MaybeArchived::Val(v) => MaybeArchivedRefMut::Val(v),
        }
    }
}

impl<T> MaybeArchivedRef<'_, T>
where
    T: Archive,
{
    pub fn get<E>(self) -> Result<T, E>
    where
        E: Source,
        T::Archived: Deserialize<T, HighDeserializer<E>>,
        T: Clone,
    {
        match self {
            MaybeArchivedRef::View(v) => rkyv::deserialize(v),
            MaybeArchivedRef::Val(v) => Ok(v.clone()),
        }
    }
}
