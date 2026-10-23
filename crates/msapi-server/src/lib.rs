//! The msapi HTTP service.
//!
//! The service is a plain function from [`http::Request`] to
//! [`http::Response`] over a SQLite connection ([`routes::handle`]). The
//! socket layer in [`serve`] is a thin adapter around it, which is what lets
//! the tests drive every route without a network.
//!
//! Every write goes through [`audit::Write`], which can only commit by also
//! recording an audit event, so there is no code path that changes data
//! without leaving a trail.

#![cfg_attr(feature = "verus", feature(proc_macro_hygiene))]

/// Without Verus, `proof! { .. }` blocks are ghost code and compile to nothing.
#[cfg(not(feature = "verus"))]
#[allow(unused_macros, reason = "used as modules gain proofs")]
macro_rules! proof {
    ($($t:tt)*) => {};
}

/// Without Verus, `proof_decl! { .. }` ghost bindings compile to nothing.
#[cfg(not(feature = "verus"))]
#[allow(unused_macros, reason = "used as modules gain proofs")]
macro_rules! proof_decl {
    ($($t:tt)*) => {};
}

pub mod audit;
pub mod auth;
pub mod db;
pub mod durable;
pub mod error;
pub mod http;
pub mod ids;
pub mod json;
pub mod passkey;
pub mod routes;
pub mod serve;
