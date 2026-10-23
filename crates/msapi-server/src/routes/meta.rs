//! Public routes: health, the API index and docs, and reference data.

use serde::Serialize;
use serde_json::json;

use msapi_core::{Region, class, world};

use crate::error::ApiError;
use crate::http::{Method, Response};

/// The agent-facing guide, served verbatim.
const DOCS: &str = include_str!("../../../../docs/api.md");

#[derive(Serialize)]
struct RegionView {
    region: Region,
    name: &'static str,
    supported: bool,
}

/// Answers a public route, or `None` if the path needs authentication.
pub fn public(method: Method, segments: &[&str]) -> Result<Option<Response>, ApiError> {
    let response = match *segments {
        ["health"] => Response::json(200, &json!({ "ok": true })),
        ["v1"] => Response::json(200, &index()),
        ["v1", "docs"] => Response::text(200, "text/markdown; charset=utf-8", DOCS),
        ["v1", "ref", "regions"] => {
            let regions: Vec<_> = Region::ALL
                .into_iter()
                .map(|r| RegionView { region: r, name: r.display_name(), supported: r.is_supported() })
                .collect();
            Response::json(200, &json!({ "regions": regions }))
        }
        ["v1", "ref", "worlds"] => Response::json(200, &json!({ "worlds": world::WORLDS })),
        ["v1", "ref", "classes"] => Response::json(200, &json!({ "classes": class::CLASSES })),
        _ => return Ok(None),
    };
    if method == Method::Get { Ok(Some(response)) } else { Err(ApiError::method_not_allowed()) }
}

fn index() -> serde_json::Value {
    json!({
        "name": "msapi",
        "version": env!("CARGO_PKG_VERSION"),
        "docs": "/v1/docs",
        "auth": "Authorization: Bearer msk_…  (everything below except /health, /v1, /v1/docs and /v1/ref/*)",
        "routes": [
            "GET    /v1/ref/regions | /v1/ref/worlds | /v1/ref/classes",
            "GET    /v1/me",
            "GET    /v1/tokens            POST /v1/tokens",
            "GET    /v1/tokens/{id}       DELETE /v1/tokens/{id}",
            "GET    /v1/audit?token_id=&include_descendants=&target_id=&action=&before=&limit=",
            "GET    /v1/accounts          POST /v1/accounts",
            "GET    /v1/accounts/{id}     PATCH /v1/accounts/{id}     DELETE /v1/accounts/{id}",
            "GET    /v1/accounts/{id}/characters      POST /v1/accounts/{id}/characters",
            "GET    /v1/characters?world=",
            "GET    /v1/characters/{id}   PATCH /v1/characters/{id}   DELETE /v1/characters/{id}",
            "GET    /v1/characters/{id}/stat   PUT /v1/characters/{id}/stat   PATCH /v1/characters/{id}/stat",
            "GET    /v1/characters/{id}/stat/history",
        ],
        "planned": super::PLANNED.iter().map(|(name, what)| json!({ "path": format!("/v1/characters/{{id}}/{name}"), "what": what })).collect::<Vec<_>>(),
    })
}
