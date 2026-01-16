Simple framework for high performance persistent local data storage.
Serialize your data structures with `rkyv` and store them in a declaratively defined `fjall` database layout for persistence.
DB reads from disk are allocated once, validated and passed straight to the user. Uses a patched version of `rancor` that adds support for `eyre` as an error source