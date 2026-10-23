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

pub mod audit;
pub mod auth;
pub mod db;
pub mod error;
pub mod http;
pub mod ids;
pub mod json;
pub mod routes;
pub mod serve;
