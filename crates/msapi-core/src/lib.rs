//! MapleStory domain types and reference data for msapi.
//!
//! This crate does no I/O. It holds the vocabulary every msapi tool shares:
//! regions and worlds, the class roster, the character stat window, and the
//! small exact-number and timestamp types those are built from. The HTTP
//! service in `msapi-server` is one consumer; the intent is that calculators
//! (and, later, a WASM build) are others.
//!
//! Three rules run through the whole crate:
//!
//! - **Absent is not zero.** A stat nobody captured is `None`, never `0`.
//!   Defaulting a missing value to zero once ranked a fake +199% upgrade first
//!   in this project's predecessor.
//! - **Numbers the game displays with decimals are stored exactly.**
//!   [`Fixed`] keeps `93.14%` as the integer `9314`, so a round trip through
//!   the API never turns it into `93.13999999999999`.
//! - **Every quantity has a unit type.** See [`units`]: STR cannot be added to
//!   DEX, and Ignore Enemy Defense cannot be added at all.

pub mod calc;
pub mod character;
pub mod class;
pub mod fixed;
pub mod ratio;
pub mod region;
pub mod stat;
pub mod time;
pub mod units;
pub mod world;

pub use character::{CharacterName, ClassLevel, Gender, Level, Liberation};
pub use class::{Class, JobType, MainStat};
pub use fixed::{ExpRate, Fixed, FixedError, Pct};
pub use ratio::Ratio;
pub use region::Region;
pub use stat::{AttackSpeed, Issue, Severity, StatBreakdown, StatBreakdowns, StatWindow};
pub use time::Timestamp;
pub use world::{DataCenter, World, WorldType};
