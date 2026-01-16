/// Declaratively define a db layout
#[macro_export]
macro_rules! db_layout {
    (
        $v:vis layout $name:ident {
            $( |$ks:ident| -> $tty:ty { $( $cons:tt )* } $(,)? )+
        }
    ) => {
        $v struct $name {
            $(
                $v $ks: $tty
            ),+
        }
        impl $name {
            $v fn new<E: ::rancor::Source>(db: &::fjall::Database) -> Result<Self, E> {
                Ok(
                    Self {
                        $(
                            $ks: {
                                let $ks =
                                    ::std::result::Result::map_err(
                                        ::fjall::Database::keyspace(db, ::std::stringify!($ks), ::std::default::Default::default)
                                    )?;
                                $( $cons )*
                            },
                        )+
                    }
                )
            }
        }
    };
}
pub use db_layout;
