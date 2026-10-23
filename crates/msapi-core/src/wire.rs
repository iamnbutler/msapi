//! Serde impls written out for types Verus checks.
//!
//! Verus refuses serde's derive on a checked type, so a checked fieldless
//! enum gets these impls instead. They behave exactly as the derive with
//! `rename_all` does, error messages included; each use has a test against
//! the derive.

/// `Serialize` and `Deserialize` for a fieldless enum with
/// `index(self) -> usize`, `from_index(usize) -> Option<Self>` and
/// `as_str(self) -> &'static str` (the wire name): what serde's derive writes.
macro_rules! unit_enum_serde {
    ($ty:ident, $count:literal, [$($wire:literal),* $(,)?]) => {
        impl serde::Serialize for $ty {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                #[allow(clippy::cast_possible_truncation, reason = "an index below the variant count")]
                let index = self.index() as u32;
                serializer.serialize_unit_variant(stringify!($ty), index, self.as_str())
            }
        }

        impl<'de> serde::Deserialize<'de> for $ty {
            fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                use serde::de;
                use std::fmt;

                const VARIANTS: &[&str] = &[$($wire),*];

                fn named(f: impl Fn(&str) -> bool) -> Option<$ty> {
                    (0..$count).filter_map($ty::from_index).find(|v| f(v.as_str()))
                }

                struct Name($ty);

                impl<'de> serde::Deserialize<'de> for Name {
                    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                        struct NameVisitor;

                        impl de::Visitor<'_> for NameVisitor {
                            type Value = Name;

                            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                                f.write_str("variant identifier")
                            }

                            fn visit_u64<E: de::Error>(self, v: u64) -> Result<Name, E> {
                                usize::try_from(v).ok().and_then($ty::from_index).map(Name).ok_or_else(|| {
                                    de::Error::invalid_value(
                                        de::Unexpected::Unsigned(v),
                                        &concat!("variant index 0 <= i < ", $count),
                                    )
                                })
                            }

                            fn visit_str<E: de::Error>(self, v: &str) -> Result<Name, E> {
                                named(|w| w == v).map(Name).ok_or_else(|| de::Error::unknown_variant(v, VARIANTS))
                            }

                            fn visit_bytes<E: de::Error>(self, v: &[u8]) -> Result<Name, E> {
                                named(|w| w.as_bytes() == v)
                                    .map(Name)
                                    .ok_or_else(|| de::Error::unknown_variant(&String::from_utf8_lossy(v), VARIANTS))
                            }
                        }

                        deserializer.deserialize_identifier(NameVisitor)
                    }
                }

                struct EnumVisitor;

                impl<'de> de::Visitor<'de> for EnumVisitor {
                    type Value = $ty;

                    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str(concat!("enum ", stringify!($ty)))
                    }

                    fn visit_enum<A: de::EnumAccess<'de>>(self, data: A) -> Result<$ty, A::Error> {
                        let (Name(v), variant) = data.variant::<Name>()?;
                        de::VariantAccess::unit_variant(variant)?;
                        Ok(v)
                    }
                }

                deserializer.deserialize_enum(stringify!($ty), VARIANTS, EnumVisitor)
            }
        }
    };
}

pub(crate) use unit_enum_serde;
