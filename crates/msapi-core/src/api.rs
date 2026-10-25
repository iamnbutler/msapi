//! The HTTP API's decisions, apart from I/O: which route a method and path
//! name, what each route is recorded as, and how request headers, query
//! parameters and bodies are read and checked. `msapi-server` does the
//! sockets, SQL and JSON around these.
//!
//! Verus checks [`route`] against [`route_spec`], the route table written
//! out case by case, and proves of it that a route is only ever reached with
//! its own method ([`method_of`]) and that `405` is only returned for a path
//! some other method serves. Path segments and header values are compared
//! as bytes against the literal [`Word`]s.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    clippy::too_many_lines,
    reason = "plain casts are what Verus checks; the tables are one arm per entry"
)]
#![allow(
    clippy::manual_range_contains,
    clippy::cast_possible_wrap,
    clippy::if_not_else,
    clippy::manual_unwrap_or_default,
    clippy::manual_unwrap_or,
    reason = "Verus has no specs for `contains` or `unwrap_or_default`; the wrapping cast is guarded and the branch order follows the spec"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

#[cfg(feature = "verus")]
use crate::query::find;
use crate::text::{char_count, parse_u64, starts_with, trim_in};
#[cfg(feature = "verus")]
use crate::text::{chars, has_prefix, parse_u64_spec, trimmed};
use crate::webauthn::bytes_eq;

/// The fixed strings the API compares against or records.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Word {
    /// `v1`.
    V1,
    /// `me`.
    Me,
    /// `tokens`.
    Tokens,
    /// `audit`.
    Audit,
    /// `accounts`.
    Accounts,
    /// `characters`.
    Characters,
    /// `stat`.
    Stat,
    /// `history`.
    History,
    /// `health`.
    Health,
    /// `docs`.
    Docs,
    /// `ref`.
    Ref,
    /// `regions`.
    Regions,
    /// `worlds`.
    Worlds,
    /// `classes`.
    Classes,
    /// `auth`.
    Auth,
    /// `passkey`.
    Passkey,
    /// `register`.
    Register,
    /// `login`.
    Login,
    /// `start`.
    Start,
    /// `finish`.
    Finish,
    /// `item-equipment`.
    ItemEquipment,
    /// `sheet`.
    Sheet,
    /// `symbol-equipment`.
    SymbolEquipment,
    /// `hyper-stat`.
    HyperStat,
    /// `ability`.
    Ability,
    /// `link-skill`.
    LinkSkill,
    /// `vmatrix`.
    Vmatrix,
    /// `hexamatrix`.
    Hexamatrix,
    /// `GET`.
    Get,
    /// `HEAD`.
    Head,
    /// `POST`.
    Post,
    /// `PUT`.
    Put,
    /// `PATCH`.
    Patch,
    /// `DELETE`.
    Delete,
    /// `OTHER`.
    Other,
    /// `me.read`.
    MeRead,
    /// `token.read`.
    TokenRead,
    /// `token.mint`.
    TokenMint,
    /// `token.revoke`.
    TokenRevoke,
    /// `audit.read`.
    AuditRead,
    /// `account.read`.
    AccountRead,
    /// `account.create`.
    AccountCreate,
    /// `account.update`.
    AccountUpdate,
    /// `account.delete`.
    AccountDelete,
    /// `character.read`.
    CharacterRead,
    /// `character.create`.
    CharacterCreate,
    /// `character.update`.
    CharacterUpdate,
    /// `character.delete`.
    CharacterDelete,
    /// `stat.read`.
    StatRead,
    /// `stat.replace`.
    StatReplace,
    /// `stat.update`.
    StatUpdate,
    /// `equipment.read`.
    EquipmentRead,
    /// `equipment.replace`.
    EquipmentReplace,
    /// `user.create`.
    UserCreate,
    /// `session.create`.
    SessionCreate,
    /// `application/json`.
    Json,
    /// `application/merge-patch+json`.
    MergePatch,
    /// `Bearer `.
    BearerUpper,
    /// `bearer `.
    BearerLower,
    /// `https://`.
    Https,
    /// `true`.
    True,
    /// `false`.
    False,
}

#[cfg(feature = "verus")]
verus! {

/// The bytes of a word.
pub open spec fn word(w: Word) -> Seq<u8> {
    match w {
        Word::V1 => seq![118u8, 49u8],
        Word::Me => seq![109u8, 101u8],
        Word::Tokens => seq![116u8, 111u8, 107u8, 101u8, 110u8, 115u8],
        Word::Audit => seq![97u8, 117u8, 100u8, 105u8, 116u8],
        Word::Accounts => seq![97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 115u8],
        Word::Characters => seq![99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 115u8],
        Word::Stat => seq![115u8, 116u8, 97u8, 116u8],
        Word::History => seq![104u8, 105u8, 115u8, 116u8, 111u8, 114u8, 121u8],
        Word::Health => seq![104u8, 101u8, 97u8, 108u8, 116u8, 104u8],
        Word::Docs => seq![100u8, 111u8, 99u8, 115u8],
        Word::Ref => seq![114u8, 101u8, 102u8],
        Word::Regions => seq![114u8, 101u8, 103u8, 105u8, 111u8, 110u8, 115u8],
        Word::Worlds => seq![119u8, 111u8, 114u8, 108u8, 100u8, 115u8],
        Word::Classes => seq![99u8, 108u8, 97u8, 115u8, 115u8, 101u8, 115u8],
        Word::Auth => seq![97u8, 117u8, 116u8, 104u8],
        Word::Passkey => seq![112u8, 97u8, 115u8, 115u8, 107u8, 101u8, 121u8],
        Word::Register => seq![114u8, 101u8, 103u8, 105u8, 115u8, 116u8, 101u8, 114u8],
        Word::Login => seq![108u8, 111u8, 103u8, 105u8, 110u8],
        Word::Start => seq![115u8, 116u8, 97u8, 114u8, 116u8],
        Word::Finish => seq![102u8, 105u8, 110u8, 105u8, 115u8, 104u8],
        Word::ItemEquipment => seq![105u8, 116u8, 101u8, 109u8, 45u8, 101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8],
        Word::Sheet => seq![115u8, 104u8, 101u8, 101u8, 116u8],
        Word::SymbolEquipment => seq![115u8, 121u8, 109u8, 98u8, 111u8, 108u8, 45u8, 101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8],
        Word::HyperStat => seq![104u8, 121u8, 112u8, 101u8, 114u8, 45u8, 115u8, 116u8, 97u8, 116u8],
        Word::Ability => seq![97u8, 98u8, 105u8, 108u8, 105u8, 116u8, 121u8],
        Word::LinkSkill => seq![108u8, 105u8, 110u8, 107u8, 45u8, 115u8, 107u8, 105u8, 108u8, 108u8],
        Word::Vmatrix => seq![118u8, 109u8, 97u8, 116u8, 114u8, 105u8, 120u8],
        Word::Hexamatrix => seq![104u8, 101u8, 120u8, 97u8, 109u8, 97u8, 116u8, 114u8, 105u8, 120u8],
        Word::Get => seq![71u8, 69u8, 84u8],
        Word::Head => seq![72u8, 69u8, 65u8, 68u8],
        Word::Post => seq![80u8, 79u8, 83u8, 84u8],
        Word::Put => seq![80u8, 85u8, 84u8],
        Word::Patch => seq![80u8, 65u8, 84u8, 67u8, 72u8],
        Word::Delete => seq![68u8, 69u8, 76u8, 69u8, 84u8, 69u8],
        Word::Other => seq![79u8, 84u8, 72u8, 69u8, 82u8],
        Word::MeRead => seq![109u8, 101u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::TokenRead => seq![116u8, 111u8, 107u8, 101u8, 110u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::TokenMint => seq![116u8, 111u8, 107u8, 101u8, 110u8, 46u8, 109u8, 105u8, 110u8, 116u8],
        Word::TokenRevoke => seq![116u8, 111u8, 107u8, 101u8, 110u8, 46u8, 114u8, 101u8, 118u8, 111u8, 107u8, 101u8],
        Word::AuditRead => seq![97u8, 117u8, 100u8, 105u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::AccountRead => seq![97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::AccountCreate => seq![97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::AccountUpdate => seq![97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 117u8, 112u8, 100u8, 97u8, 116u8, 101u8],
        Word::AccountDelete => seq![97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 100u8, 101u8, 108u8, 101u8, 116u8, 101u8],
        Word::CharacterRead => seq![99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::CharacterCreate => seq![99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::CharacterUpdate => seq![99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 117u8, 112u8, 100u8, 97u8, 116u8, 101u8],
        Word::CharacterDelete => seq![99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 100u8, 101u8, 108u8, 101u8, 116u8, 101u8],
        Word::StatRead => seq![115u8, 116u8, 97u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::StatReplace => seq![115u8, 116u8, 97u8, 116u8, 46u8, 114u8, 101u8, 112u8, 108u8, 97u8, 99u8, 101u8],
        Word::StatUpdate => seq![115u8, 116u8, 97u8, 116u8, 46u8, 117u8, 112u8, 100u8, 97u8, 116u8, 101u8],
        Word::EquipmentRead => seq![101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::EquipmentReplace => seq![101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8, 46u8, 114u8, 101u8, 112u8, 108u8, 97u8, 99u8, 101u8],
        Word::UserCreate => seq![117u8, 115u8, 101u8, 114u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::SessionCreate => seq![115u8, 101u8, 115u8, 115u8, 105u8, 111u8, 110u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::Json => seq![97u8, 112u8, 112u8, 108u8, 105u8, 99u8, 97u8, 116u8, 105u8, 111u8, 110u8, 47u8, 106u8, 115u8, 111u8, 110u8],
        Word::MergePatch => seq![97u8, 112u8, 112u8, 108u8, 105u8, 99u8, 97u8, 116u8, 105u8, 111u8, 110u8, 47u8, 109u8, 101u8, 114u8, 103u8, 101u8, 45u8, 112u8, 97u8, 116u8, 99u8, 104u8, 43u8, 106u8, 115u8, 111u8, 110u8],
        Word::BearerUpper => seq![66u8, 101u8, 97u8, 114u8, 101u8, 114u8, 32u8],
        Word::BearerLower => seq![98u8, 101u8, 97u8, 114u8, 101u8, 114u8, 32u8],
        Word::Https => seq![104u8, 116u8, 116u8, 112u8, 115u8, 58u8, 47u8, 47u8],
        Word::True => seq![116u8, 114u8, 117u8, 101u8],
        Word::False => seq![102u8, 97u8, 108u8, 115u8, 101u8],
    }
}

} // verus!

/// The bytes of a word.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r@ == word(w)))]
#[must_use]
#[rustfmt::skip]
pub fn word_bytes(w: Word) -> &'static [u8] {
    let r: &'static [u8] = match w {
        Word::V1 => &[118u8, 49u8],
        Word::Me => &[109u8, 101u8],
        Word::Tokens => &[116u8, 111u8, 107u8, 101u8, 110u8, 115u8],
        Word::Audit => &[97u8, 117u8, 100u8, 105u8, 116u8],
        Word::Accounts => &[97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 115u8],
        Word::Characters => &[99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 115u8],
        Word::Stat => &[115u8, 116u8, 97u8, 116u8],
        Word::History => &[104u8, 105u8, 115u8, 116u8, 111u8, 114u8, 121u8],
        Word::Health => &[104u8, 101u8, 97u8, 108u8, 116u8, 104u8],
        Word::Docs => &[100u8, 111u8, 99u8, 115u8],
        Word::Ref => &[114u8, 101u8, 102u8],
        Word::Regions => &[114u8, 101u8, 103u8, 105u8, 111u8, 110u8, 115u8],
        Word::Worlds => &[119u8, 111u8, 114u8, 108u8, 100u8, 115u8],
        Word::Classes => &[99u8, 108u8, 97u8, 115u8, 115u8, 101u8, 115u8],
        Word::Auth => &[97u8, 117u8, 116u8, 104u8],
        Word::Passkey => &[112u8, 97u8, 115u8, 115u8, 107u8, 101u8, 121u8],
        Word::Register => &[114u8, 101u8, 103u8, 105u8, 115u8, 116u8, 101u8, 114u8],
        Word::Login => &[108u8, 111u8, 103u8, 105u8, 110u8],
        Word::Start => &[115u8, 116u8, 97u8, 114u8, 116u8],
        Word::Finish => &[102u8, 105u8, 110u8, 105u8, 115u8, 104u8],
        Word::ItemEquipment => &[105u8, 116u8, 101u8, 109u8, 45u8, 101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8],
        Word::Sheet => &[115u8, 104u8, 101u8, 101u8, 116u8],
        Word::SymbolEquipment => &[115u8, 121u8, 109u8, 98u8, 111u8, 108u8, 45u8, 101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8],
        Word::HyperStat => &[104u8, 121u8, 112u8, 101u8, 114u8, 45u8, 115u8, 116u8, 97u8, 116u8],
        Word::Ability => &[97u8, 98u8, 105u8, 108u8, 105u8, 116u8, 121u8],
        Word::LinkSkill => &[108u8, 105u8, 110u8, 107u8, 45u8, 115u8, 107u8, 105u8, 108u8, 108u8],
        Word::Vmatrix => &[118u8, 109u8, 97u8, 116u8, 114u8, 105u8, 120u8],
        Word::Hexamatrix => &[104u8, 101u8, 120u8, 97u8, 109u8, 97u8, 116u8, 114u8, 105u8, 120u8],
        Word::Get => &[71u8, 69u8, 84u8],
        Word::Head => &[72u8, 69u8, 65u8, 68u8],
        Word::Post => &[80u8, 79u8, 83u8, 84u8],
        Word::Put => &[80u8, 85u8, 84u8],
        Word::Patch => &[80u8, 65u8, 84u8, 67u8, 72u8],
        Word::Delete => &[68u8, 69u8, 76u8, 69u8, 84u8, 69u8],
        Word::Other => &[79u8, 84u8, 72u8, 69u8, 82u8],
        Word::MeRead => &[109u8, 101u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::TokenRead => &[116u8, 111u8, 107u8, 101u8, 110u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::TokenMint => &[116u8, 111u8, 107u8, 101u8, 110u8, 46u8, 109u8, 105u8, 110u8, 116u8],
        Word::TokenRevoke => &[116u8, 111u8, 107u8, 101u8, 110u8, 46u8, 114u8, 101u8, 118u8, 111u8, 107u8, 101u8],
        Word::AuditRead => &[97u8, 117u8, 100u8, 105u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::AccountRead => &[97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::AccountCreate => &[97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::AccountUpdate => &[97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 117u8, 112u8, 100u8, 97u8, 116u8, 101u8],
        Word::AccountDelete => &[97u8, 99u8, 99u8, 111u8, 117u8, 110u8, 116u8, 46u8, 100u8, 101u8, 108u8, 101u8, 116u8, 101u8],
        Word::CharacterRead => &[99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::CharacterCreate => &[99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::CharacterUpdate => &[99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 117u8, 112u8, 100u8, 97u8, 116u8, 101u8],
        Word::CharacterDelete => &[99u8, 104u8, 97u8, 114u8, 97u8, 99u8, 116u8, 101u8, 114u8, 46u8, 100u8, 101u8, 108u8, 101u8, 116u8, 101u8],
        Word::StatRead => &[115u8, 116u8, 97u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::StatReplace => &[115u8, 116u8, 97u8, 116u8, 46u8, 114u8, 101u8, 112u8, 108u8, 97u8, 99u8, 101u8],
        Word::StatUpdate => &[115u8, 116u8, 97u8, 116u8, 46u8, 117u8, 112u8, 100u8, 97u8, 116u8, 101u8],
        Word::EquipmentRead => &[101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8, 46u8, 114u8, 101u8, 97u8, 100u8],
        Word::EquipmentReplace => &[101u8, 113u8, 117u8, 105u8, 112u8, 109u8, 101u8, 110u8, 116u8, 46u8, 114u8, 101u8, 112u8, 108u8, 97u8, 99u8, 101u8],
        Word::UserCreate => &[117u8, 115u8, 101u8, 114u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::SessionCreate => &[115u8, 101u8, 115u8, 115u8, 105u8, 111u8, 110u8, 46u8, 99u8, 114u8, 101u8, 97u8, 116u8, 101u8],
        Word::Json => &[97u8, 112u8, 112u8, 108u8, 105u8, 99u8, 97u8, 116u8, 105u8, 111u8, 110u8, 47u8, 106u8, 115u8, 111u8, 110u8],
        Word::MergePatch => &[97u8, 112u8, 112u8, 108u8, 105u8, 99u8, 97u8, 116u8, 105u8, 111u8, 110u8, 47u8, 109u8, 101u8, 114u8, 103u8, 101u8, 45u8, 112u8, 97u8, 116u8, 99u8, 104u8, 43u8, 106u8, 115u8, 111u8, 110u8],
        Word::BearerUpper => &[66u8, 101u8, 97u8, 114u8, 101u8, 114u8, 32u8],
        Word::BearerLower => &[98u8, 101u8, 97u8, 114u8, 101u8, 114u8, 32u8],
        Word::Https => &[104u8, 116u8, 116u8, 112u8, 115u8, 58u8, 47u8, 47u8],
        Word::True => &[116u8, 114u8, 117u8, 101u8],
        Word::False => &[102u8, 97u8, 108u8, 115u8, 101u8],
    };
    proof! { assert(r@ =~= word(w)); }
    r
}

/// Whether `s` is the word `w`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (s@ == word(w))))]
#[must_use]
pub fn is(s: &[u8], w: Word) -> bool {
    bytes_eq(s, word_bytes(w))
}

/// The HTTP methods the API distinguishes.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Method {
    /// GET (and HEAD).
    Get,
    /// POST.
    Post,
    /// PUT.
    Put,
    /// PATCH.
    Patch,
    /// DELETE.
    Delete,
    /// Anything else.
    Other,
}

#[cfg(feature = "verus")]
verus! {

/// The method a request line's method name means.
pub open spec fn method_spec(s: Seq<u8>) -> Method {
    if s == word(Word::Get) || s == word(Word::Head) {
        Method::Get
    } else if s == word(Word::Post) {
        Method::Post
    } else if s == word(Word::Put) {
        Method::Put
    } else if s == word(Word::Patch) {
        Method::Patch
    } else if s == word(Word::Delete) {
        Method::Delete
    } else {
        Method::Other
    }
}

/// The name a method is logged and audited under.
pub open spec fn method_word(m: Method) -> Word {
    match m {
        Method::Get => Word::Get,
        Method::Post => Word::Post,
        Method::Put => Word::Put,
        Method::Patch => Word::Patch,
        Method::Delete => Word::Delete,
        Method::Other => Word::Other,
    }
}

/// Whether a method can change data.
pub open spec fn writes(m: Method) -> bool {
    m == Method::Post || m == Method::Put || m == Method::Patch || m == Method::Delete
}

} // verus!

#[cfg_attr(feature = "verus", verus_verify)]
impl Method {
    /// The method a request line's method name means: `GET` and `HEAD` are
    /// [`Method::Get`]; unknown names are [`Method::Other`].
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r == method_spec(s@)))]
    #[must_use]
    pub fn parse(s: &[u8]) -> Self {
        if is(s, Word::Get) || is(s, Word::Head) {
            Self::Get
        } else if is(s, Word::Post) {
            Self::Post
        } else if is(s, Word::Put) {
            Self::Put
        } else if is(s, Word::Patch) {
            Self::Patch
        } else if is(s, Word::Delete) {
            Self::Delete
        } else {
            Self::Other
        }
    }

    /// The name the method is logged and audited under.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r == method_word(self)))]
    #[must_use]
    pub const fn word(self) -> Word {
        match self {
            Self::Get => Word::Get,
            Self::Post => Word::Post,
            Self::Put => Word::Put,
            Self::Patch => Word::Patch,
            Self::Delete => Word::Delete,
            Self::Other => Word::Other,
        }
    }

    /// Whether the method can change data.
    #[cfg_attr(feature = "verus", verus_spec(r => ensures r == writes(self)))]
    #[must_use]
    pub const fn is_write(self) -> bool {
        matches!(self, Self::Post | Self::Put | Self::Patch | Self::Delete)
    }
}

/// Every route. Where a route has an `{id}`, it is path segment 2.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Route {
    /// `GET /health`.
    Health,
    /// `GET /v1`.
    Index,
    /// `GET /v1/docs`.
    Docs,
    /// `GET /v1/ref/regions`.
    RefRegions,
    /// `GET /v1/ref/worlds`.
    RefWorlds,
    /// `GET /v1/ref/classes`.
    RefClasses,
    /// `POST /v1/auth/passkey/register/start`.
    RegisterStart,
    /// `POST /v1/auth/passkey/register/finish`.
    RegisterFinish,
    /// `POST /v1/auth/passkey/login/start`.
    LoginStart,
    /// `POST /v1/auth/passkey/login/finish`.
    LoginFinish,
    /// `GET /v1/me`.
    Me,
    /// `GET /v1/tokens`.
    ListTokens,
    /// `POST /v1/tokens`.
    MintToken,
    /// `GET /v1/tokens/{id}`.
    GetToken,
    /// `DELETE /v1/tokens/{id}`.
    RevokeToken,
    /// `GET /v1/audit`.
    Audit,
    /// `GET /v1/accounts`.
    ListAccounts,
    /// `POST /v1/accounts`.
    CreateAccount,
    /// `GET /v1/accounts/{id}`.
    GetAccount,
    /// `PATCH /v1/accounts/{id}`.
    UpdateAccount,
    /// `DELETE /v1/accounts/{id}`.
    DeleteAccount,
    /// `GET /v1/accounts/{id}/characters`.
    ListAccountCharacters,
    /// `POST /v1/accounts/{id}/characters`.
    CreateCharacter,
    /// `GET /v1/characters`.
    ListCharacters,
    /// `GET /v1/characters/{id}`.
    GetCharacter,
    /// `PATCH /v1/characters/{id}`.
    UpdateCharacter,
    /// `DELETE /v1/characters/{id}`.
    DeleteCharacter,
    /// `GET /v1/characters/{id}/stat`.
    GetStat,
    /// `PUT /v1/characters/{id}/stat`.
    ReplaceStat,
    /// `PATCH /v1/characters/{id}/stat`.
    UpdateStat,
    /// `GET /v1/characters/{id}/stat/history`.
    StatHistory,
    /// `GET /v1/characters/{id}/item-equipment`.
    GetItemEquipment,
    /// `PUT /v1/characters/{id}/item-equipment`.
    ReplaceItemEquipment,
    /// `GET /v1/characters/{id}/item-equipment/history`.
    ItemEquipmentHistory,
    /// `GET /v1/characters/{id}/sheet`.
    CharacterSheet,
    /// `GET /v1/characters/{id}/{resource}` for a resource in [`PLANNED`],
    /// by its position there.
    Planned(u8),
}

/// What a method and path name.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Routed {
    /// This route.
    Found(Route),
    /// The path exists, but not for this method: `405`.
    NotAllowed,
    /// No such path: `404`.
    NotFound,
}

/// Character resources the Nexon Open API has that msapi will add later, in
/// the order [`Route::Planned`] numbers them.
#[cfg_attr(feature = "verus", verus_verify)]
pub const PLANNED: [Word; 6] =
    [Word::SymbolEquipment, Word::HyperStat, Word::Ability, Word::LinkSkill, Word::Vmatrix, Word::Hexamatrix];

#[cfg(feature = "verus")]
verus! {

/// Segment `i` of `s` is the word `w`.
pub open spec fn at(s: Seq<&[u8]>, i: int, w: Word) -> bool {
    0 <= i < s.len() && s[i]@ == word(w)
}

/// The planned resource `r` names, by position in [`PLANNED`].
pub open spec fn planned_spec(r: Seq<u8>) -> Option<u8> {
    if r == word(Word::SymbolEquipment) {
        Some(0)
    } else if r == word(Word::HyperStat) {
        Some(1)
    } else if r == word(Word::Ability) {
        Some(2)
    } else if r == word(Word::LinkSkill) {
        Some(3)
    } else if r == word(Word::Vmatrix) {
        Some(4)
    } else if r == word(Word::Hexamatrix) {
        Some(5)
    } else {
        None
    }
}

/// `r` if `m` is `want`, else `405`.
pub open spec fn one(m: Method, want: Method, r: Route) -> Routed {
    if m == want { Routed::Found(r) } else { Routed::NotAllowed }
}

/// The route of the two whose method is `m`, else `405`.
pub open spec fn two(m: Method, m1: Method, r1: Route, m2: Method, r2: Route) -> Routed {
    if m == m1 { Routed::Found(r1) } else { one(m, m2, r2) }
}

/// The route of the three whose method is `m`, else `405`.
pub open spec fn three(m: Method, m1: Method, r1: Route, m2: Method, r2: Route, m3: Method, r3: Route) -> Routed {
    if m == m1 { Routed::Found(r1) } else { two(m, m2, r2, m3, r3) }
}

/// The public (unauthenticated, GET-only) route a path names.
pub open spec fn public_spec(s: Seq<&[u8]>) -> Option<Route> {
    let n = s.len();
    if n == 1 && at(s, 0, Word::Health) {
        Some(Route::Health)
    } else if n == 1 && at(s, 0, Word::V1) {
        Some(Route::Index)
    } else if n == 2 && at(s, 0, Word::V1) && at(s, 1, Word::Docs) {
        Some(Route::Docs)
    } else if n == 3 && at(s, 0, Word::V1) && at(s, 1, Word::Ref) && at(s, 2, Word::Regions) {
        Some(Route::RefRegions)
    } else if n == 3 && at(s, 0, Word::V1) && at(s, 1, Word::Ref) && at(s, 2, Word::Worlds) {
        Some(Route::RefWorlds)
    } else if n == 3 && at(s, 0, Word::V1) && at(s, 1, Word::Ref) && at(s, 2, Word::Classes) {
        Some(Route::RefClasses)
    } else {
        None
    }
}

/// Whether a path is under `/v1/auth/passkey/`.
pub open spec fn passkey_path(s: Seq<&[u8]>) -> bool {
    s.len() >= 3 && at(s, 0, Word::V1) && at(s, 1, Word::Auth) && at(s, 2, Word::Passkey)
}

/// The passkey step a path under `/v1/auth/passkey/` names.
pub open spec fn passkey_spec(s: Seq<&[u8]>) -> Option<Route> {
    if s.len() == 5 && at(s, 3, Word::Register) && at(s, 4, Word::Start) {
        Some(Route::RegisterStart)
    } else if s.len() == 5 && at(s, 3, Word::Register) && at(s, 4, Word::Finish) {
        Some(Route::RegisterFinish)
    } else if s.len() == 5 && at(s, 3, Word::Login) && at(s, 4, Word::Start) {
        Some(Route::LoginStart)
    } else if s.len() == 5 && at(s, 3, Word::Login) && at(s, 4, Word::Finish) {
        Some(Route::LoginFinish)
    } else {
        None
    }
}

/// The authenticated routes.
pub open spec fn api_spec(m: Method, s: Seq<&[u8]>) -> Routed {
    let n = s.len();
    if n < 2 || !at(s, 0, Word::V1) {
        Routed::NotFound
    } else if n == 2 && at(s, 1, Word::Me) {
        one(m, Method::Get, Route::Me)
    } else if n == 2 && at(s, 1, Word::Tokens) {
        two(m, Method::Get, Route::ListTokens, Method::Post, Route::MintToken)
    } else if n == 3 && at(s, 1, Word::Tokens) {
        two(m, Method::Get, Route::GetToken, Method::Delete, Route::RevokeToken)
    } else if n == 2 && at(s, 1, Word::Audit) {
        one(m, Method::Get, Route::Audit)
    } else if n == 2 && at(s, 1, Word::Accounts) {
        two(m, Method::Get, Route::ListAccounts, Method::Post, Route::CreateAccount)
    } else if n == 3 && at(s, 1, Word::Accounts) {
        three(m, Method::Get, Route::GetAccount, Method::Patch, Route::UpdateAccount, Method::Delete, Route::DeleteAccount)
    } else if n == 4 && at(s, 1, Word::Accounts) && at(s, 3, Word::Characters) {
        two(m, Method::Get, Route::ListAccountCharacters, Method::Post, Route::CreateCharacter)
    } else if n == 2 && at(s, 1, Word::Characters) {
        one(m, Method::Get, Route::ListCharacters)
    } else if n == 3 && at(s, 1, Word::Characters) {
        three(m, Method::Get, Route::GetCharacter, Method::Patch, Route::UpdateCharacter, Method::Delete, Route::DeleteCharacter)
    } else if n == 4 && at(s, 1, Word::Characters) && at(s, 3, Word::Stat) {
        three(m, Method::Get, Route::GetStat, Method::Put, Route::ReplaceStat, Method::Patch, Route::UpdateStat)
    } else if n == 5 && at(s, 1, Word::Characters) && at(s, 3, Word::Stat) && at(s, 4, Word::History) {
        one(m, Method::Get, Route::StatHistory)
    } else if n == 4 && at(s, 1, Word::Characters) && at(s, 3, Word::ItemEquipment) {
        two(m, Method::Get, Route::GetItemEquipment, Method::Put, Route::ReplaceItemEquipment)
    } else if n == 5 && at(s, 1, Word::Characters) && at(s, 3, Word::ItemEquipment) && at(s, 4, Word::History) {
        one(m, Method::Get, Route::ItemEquipmentHistory)
    } else if n == 4 && at(s, 1, Word::Characters) && at(s, 3, Word::Sheet) {
        one(m, Method::Get, Route::CharacterSheet)
    } else if n == 4 && at(s, 1, Word::Characters) {
        match planned_spec(s[3]@) {
            Some(k) => one(m, Method::Get, Route::Planned(k)),
            None => Routed::NotFound,
        }
    } else {
        Routed::NotFound
    }
}

/// The route table: public routes first (GET only), then the passkey
/// ceremony (POST only, `405` for any other method under its prefix), then
/// the authenticated routes.
pub open spec fn route_spec(m: Method, s: Seq<&[u8]>) -> Routed {
    match public_spec(s) {
        Some(r) => one(m, Method::Get, r),
        None => if passkey_path(s) {
            if m != Method::Post {
                Routed::NotAllowed
            } else {
                match passkey_spec(s) {
                    Some(r) => Routed::Found(r),
                    None => Routed::NotFound,
                }
            }
        } else {
            api_spec(m, s)
        },
    }
}

/// The one method each route answers.
pub open spec fn method_of(r: Route) -> Method {
    match r {
        Route::RegisterStart | Route::RegisterFinish | Route::LoginStart | Route::LoginFinish
        | Route::MintToken | Route::CreateAccount | Route::CreateCharacter => Method::Post,
        Route::RevokeToken | Route::DeleteAccount | Route::DeleteCharacter => Method::Delete,
        Route::UpdateAccount | Route::UpdateCharacter | Route::UpdateStat => Method::Patch,
        Route::ReplaceStat | Route::ReplaceItemEquipment => Method::Put,
        _ => Method::Get,
    }
}

/// Some method reaches a route at path `s`.
pub open spec fn path_exists(s: Seq<&[u8]>) -> bool {
    route_spec(Method::Get, s) is Found || route_spec(Method::Post, s) is Found
        || route_spec(Method::Put, s) is Found || route_spec(Method::Patch, s) is Found
        || route_spec(Method::Delete, s) is Found
}

/// The audit action a route is recorded as, if it is audited.
pub open spec fn action_spec(r: Route) -> Option<Word> {
    match r {
        Route::Health | Route::Index | Route::Docs | Route::RefRegions | Route::RefWorlds | Route::RefClasses
        | Route::RegisterStart | Route::LoginStart => None,
        Route::RegisterFinish => Some(Word::UserCreate),
        Route::LoginFinish => Some(Word::SessionCreate),
        Route::Me => Some(Word::MeRead),
        Route::ListTokens | Route::GetToken => Some(Word::TokenRead),
        Route::MintToken => Some(Word::TokenMint),
        Route::RevokeToken => Some(Word::TokenRevoke),
        Route::Audit => Some(Word::AuditRead),
        Route::ListAccounts | Route::GetAccount => Some(Word::AccountRead),
        Route::CreateAccount => Some(Word::AccountCreate),
        Route::UpdateAccount => Some(Word::AccountUpdate),
        Route::DeleteAccount => Some(Word::AccountDelete),
        Route::ListAccountCharacters | Route::ListCharacters | Route::GetCharacter | Route::CharacterSheet | Route::Planned(_) => {
            Some(Word::CharacterRead)
        },
        Route::CreateCharacter => Some(Word::CharacterCreate),
        Route::UpdateCharacter => Some(Word::CharacterUpdate),
        Route::DeleteCharacter => Some(Word::CharacterDelete),
        Route::GetStat | Route::StatHistory => Some(Word::StatRead),
        Route::ReplaceStat => Some(Word::StatReplace),
        Route::UpdateStat => Some(Word::StatUpdate),
        Route::GetItemEquipment | Route::ItemEquipmentHistory => Some(Word::EquipmentRead),
        Route::ReplaceItemEquipment => Some(Word::EquipmentReplace),
    }
}

/// Whether an audit action only reads.
pub open spec fn reads(a: Word) -> bool {
    a == Word::MeRead || a == Word::TokenRead || a == Word::AuditRead || a == Word::AccountRead
        || a == Word::CharacterRead || a == Word::StatRead || a == Word::EquipmentRead
}

/// A route is only reached with its own method; a `405` path is one some
/// other method reaches, or under `/v1/auth/passkey/` (where every method but
/// POST is refused before the step is looked at); and a route's audit action reads exactly when its
/// method cannot write.
pub proof fn lemma_route(m: Method, s: Seq<&[u8]>)
    ensures
        route_spec(m, s) matches Routed::Found(r) ==> m == method_of(r),
        route_spec(m, s) is NotAllowed ==> path_exists(s) || passkey_path(s),
        forall|r: Route| (#[trigger] action_spec(r)) matches Some(a) ==> (reads(a) <==> !writes(method_of(r))),
{
}

} // verus!

/// Whether two methods are the same.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (a == b)))]
#[must_use]
pub const fn same(a: Method, b: Method) -> bool {
    matches!(
        (a, b),
        (Method::Get, Method::Get)
            | (Method::Post, Method::Post)
            | (Method::Put, Method::Put)
            | (Method::Patch, Method::Patch)
            | (Method::Delete, Method::Delete)
            | (Method::Other, Method::Other)
    )
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == one(m, want, route)))]
fn pick1(m: Method, want: Method, route: Route) -> Routed {
    if same(m, want) { Routed::Found(route) } else { Routed::NotAllowed }
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == two(m, m1, r1, m2, r2)))]
fn pick2(m: Method, m1: Method, r1: Route, m2: Method, r2: Route) -> Routed {
    if same(m, m1) { Routed::Found(r1) } else { pick1(m, m2, r2) }
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == three(m, m1, r1, m2, r2, m3, r3)))]
#[allow(clippy::too_many_arguments, reason = "three method and route pairs")]
fn pick3(m: Method, m1: Method, r1: Route, m2: Method, r2: Route, m3: Method, r3: Route) -> Routed {
    if same(m, m1) { Routed::Found(r1) } else { pick2(m, m2, r2, m3, r3) }
}

/// Whether segment `i` of `s` is the word `w`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == at(s@, i as int, w)))]
fn seg_is(s: &[&[u8]], i: usize, w: Word) -> bool {
    i < s.len() && is(s[i], w)
}

/// The planned resource `r` names, by position in [`PLANNED`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(k => ensures k == planned_spec(r@)))]
#[must_use]
pub fn planned(r: &[u8]) -> Option<u8> {
    if is(r, Word::SymbolEquipment) {
        Some(0)
    } else if is(r, Word::HyperStat) {
        Some(1)
    } else if is(r, Word::Ability) {
        Some(2)
    } else if is(r, Word::LinkSkill) {
        Some(3)
    } else if is(r, Word::Vmatrix) {
        Some(4)
    } else if is(r, Word::Hexamatrix) {
        Some(5)
    } else {
        None
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == public_spec(s@)))]
fn public(s: &[&[u8]]) -> Option<Route> {
    let n = s.len();
    if n == 1 && seg_is(s, 0, Word::Health) {
        Some(Route::Health)
    } else if n == 1 && seg_is(s, 0, Word::V1) {
        Some(Route::Index)
    } else if n == 2 && seg_is(s, 0, Word::V1) && seg_is(s, 1, Word::Docs) {
        Some(Route::Docs)
    } else if n == 3 && seg_is(s, 0, Word::V1) && seg_is(s, 1, Word::Ref) && seg_is(s, 2, Word::Regions) {
        Some(Route::RefRegions)
    } else if n == 3 && seg_is(s, 0, Word::V1) && seg_is(s, 1, Word::Ref) && seg_is(s, 2, Word::Worlds) {
        Some(Route::RefWorlds)
    } else if n == 3 && seg_is(s, 0, Word::V1) && seg_is(s, 1, Word::Ref) && seg_is(s, 2, Word::Classes) {
        Some(Route::RefClasses)
    } else {
        None
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == passkey_spec(s@)))]
fn passkey(s: &[&[u8]]) -> Option<Route> {
    let n = s.len();
    if n == 5 && seg_is(s, 3, Word::Register) && seg_is(s, 4, Word::Start) {
        Some(Route::RegisterStart)
    } else if n == 5 && seg_is(s, 3, Word::Register) && seg_is(s, 4, Word::Finish) {
        Some(Route::RegisterFinish)
    } else if n == 5 && seg_is(s, 3, Word::Login) && seg_is(s, 4, Word::Start) {
        Some(Route::LoginStart)
    } else if n == 5 && seg_is(s, 3, Word::Login) && seg_is(s, 4, Word::Finish) {
        Some(Route::LoginFinish)
    } else {
        None
    }
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == api_spec(m, s@)))]
fn api(m: Method, s: &[&[u8]]) -> Routed {
    use Method::{Delete, Get, Patch, Post, Put};
    let n = s.len();
    if n < 2 || !seg_is(s, 0, Word::V1) {
        Routed::NotFound
    } else if n == 2 && seg_is(s, 1, Word::Me) {
        pick1(m, Get, Route::Me)
    } else if n == 2 && seg_is(s, 1, Word::Tokens) {
        pick2(m, Get, Route::ListTokens, Post, Route::MintToken)
    } else if n == 3 && seg_is(s, 1, Word::Tokens) {
        pick2(m, Get, Route::GetToken, Delete, Route::RevokeToken)
    } else if n == 2 && seg_is(s, 1, Word::Audit) {
        pick1(m, Get, Route::Audit)
    } else if n == 2 && seg_is(s, 1, Word::Accounts) {
        pick2(m, Get, Route::ListAccounts, Post, Route::CreateAccount)
    } else if n == 3 && seg_is(s, 1, Word::Accounts) {
        pick3(m, Get, Route::GetAccount, Patch, Route::UpdateAccount, Delete, Route::DeleteAccount)
    } else if n == 4 && seg_is(s, 1, Word::Accounts) && seg_is(s, 3, Word::Characters) {
        pick2(m, Get, Route::ListAccountCharacters, Post, Route::CreateCharacter)
    } else if n == 2 && seg_is(s, 1, Word::Characters) {
        pick1(m, Get, Route::ListCharacters)
    } else if n == 3 && seg_is(s, 1, Word::Characters) {
        pick3(m, Get, Route::GetCharacter, Patch, Route::UpdateCharacter, Delete, Route::DeleteCharacter)
    } else if n == 4 && seg_is(s, 1, Word::Characters) && seg_is(s, 3, Word::Stat) {
        pick3(m, Get, Route::GetStat, Put, Route::ReplaceStat, Patch, Route::UpdateStat)
    } else if n == 5 && seg_is(s, 1, Word::Characters) && seg_is(s, 3, Word::Stat) && seg_is(s, 4, Word::History) {
        pick1(m, Get, Route::StatHistory)
    } else if n == 4 && seg_is(s, 1, Word::Characters) && seg_is(s, 3, Word::ItemEquipment) {
        pick2(m, Get, Route::GetItemEquipment, Put, Route::ReplaceItemEquipment)
    } else if n == 5
        && seg_is(s, 1, Word::Characters)
        && seg_is(s, 3, Word::ItemEquipment)
        && seg_is(s, 4, Word::History)
    {
        pick1(m, Get, Route::ItemEquipmentHistory)
    } else if n == 4 && seg_is(s, 1, Word::Characters) && seg_is(s, 3, Word::Sheet) {
        pick1(m, Get, Route::CharacterSheet)
    } else if n == 4 && seg_is(s, 1, Word::Characters) {
        match planned(s[3]) {
            Some(k) => pick1(m, Get, Route::Planned(k)),
            None => Routed::NotFound,
        }
    } else {
        Routed::NotFound
    }
}

/// What `m` and the path segments `s` (the path split on `/`, empty
/// segments dropped) name: [`route_spec`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r == route_spec(m, s@),
        r matches Routed::Found(x) ==> m == method_of(x),
        r is NotAllowed ==> path_exists(s@) || passkey_path(s@),
))]
#[must_use]
pub fn route(m: Method, s: &[&[u8]]) -> Routed {
    proof! { lemma_route(m, s@); }
    match public(s) {
        Some(r) => pick1(m, Method::Get, r),
        None => {
            if s.len() >= 3 && seg_is(s, 0, Word::V1) && seg_is(s, 1, Word::Auth) && seg_is(s, 2, Word::Passkey) {
                if !same(m, Method::Post) {
                    Routed::NotAllowed
                } else {
                    match passkey(s) {
                        Some(r) => Routed::Found(r),
                        None => Routed::NotFound,
                    }
                }
            } else {
                api(m, s)
            }
        }
    }
}

/// The audit action a route is recorded as, if it is audited.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(a => ensures a == action_spec(r)))]
#[must_use]
pub const fn action(r: Route) -> Option<Word> {
    match r {
        Route::Health
        | Route::Index
        | Route::Docs
        | Route::RefRegions
        | Route::RefWorlds
        | Route::RefClasses
        | Route::RegisterStart
        | Route::LoginStart => None,
        Route::RegisterFinish => Some(Word::UserCreate),
        Route::LoginFinish => Some(Word::SessionCreate),
        Route::Me => Some(Word::MeRead),
        Route::ListTokens | Route::GetToken => Some(Word::TokenRead),
        Route::MintToken => Some(Word::TokenMint),
        Route::RevokeToken => Some(Word::TokenRevoke),
        Route::Audit => Some(Word::AuditRead),
        Route::ListAccounts | Route::GetAccount => Some(Word::AccountRead),
        Route::CreateAccount => Some(Word::AccountCreate),
        Route::UpdateAccount => Some(Word::AccountUpdate),
        Route::DeleteAccount => Some(Word::AccountDelete),
        Route::ListAccountCharacters
        | Route::ListCharacters
        | Route::GetCharacter
        | Route::CharacterSheet
        | Route::Planned(_) => Some(Word::CharacterRead),
        Route::CreateCharacter => Some(Word::CharacterCreate),
        Route::UpdateCharacter => Some(Word::CharacterUpdate),
        Route::DeleteCharacter => Some(Word::CharacterDelete),
        Route::GetStat | Route::StatHistory => Some(Word::StatRead),
        Route::ReplaceStat => Some(Word::StatReplace),
        Route::UpdateStat => Some(Word::StatUpdate),
        Route::GetItemEquipment | Route::ItemEquipmentHistory => Some(Word::EquipmentRead),
        Route::ReplaceItemEquipment => Some(Word::EquipmentReplace),
    }
}

/// The largest request body accepted, in bytes.
#[cfg_attr(feature = "verus", verus_verify)]
pub const MAX_BODY: usize = 256 * 1024;

/// The number of milliseconds a passkey session lasts: thirty days.
#[cfg_attr(feature = "verus", verus_verify)]
pub const SESSION_MS: i64 = 30 * 24 * 60 * 60 * 1000;

#[cfg(feature = "verus")]
verus! {

/// The token an `Authorization` header carries: after `Bearer ` (or
/// `bearer `), trimmed.
pub open spec fn bearer_spec(h: Seq<u8>) -> Option<Seq<u8>> {
    if has_prefix(h, word(Word::BearerUpper)) || has_prefix(h, word(Word::BearerLower)) {
        Some(trimmed(h.skip(7)))
    } else {
        None
    }
}

/// The page size `limit` asks for: 50 when absent, else its value if 1-200;
/// text that is not a number counts as 0, which is refused.
pub open spec fn page_limit_spec(limit: Option<Seq<u8>>) -> Option<u32> {
    let n: u64 = match limit {
        None => 50,
        Some(t) => match parse_u64_spec(t) {
            Some(n) => n,
            None => 0,
        },
    };
    if 1 <= n <= 200 { Some(n as u32) } else { None }
}

/// The `include_descendants` flag: absent or `false` is false, `true` is
/// true, anything else is refused.
pub open spec fn flag_spec(v: Option<Seq<u8>>) -> Option<bool> {
    match v {
        None => Some(false),
        Some(t) => if t == word(Word::True) {
            Some(true)
        } else if t == word(Word::False) {
            Some(false)
        } else {
            None
        },
    }
}

/// A content type the API reads JSON bodies under.
pub open spec fn json_type_spec(ct: Seq<u8>) -> bool {
    has_prefix(ct, word(Word::Json)) || has_prefix(ct, word(Word::MergePatch))
}

} // verus!

/// The token an `Authorization` header carries, as a range of `h`: after
/// `Bearer ` or `bearer `, trimmed.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Some((a, b)) => a <= b <= h.len() && bearer_spec(h@) == Some(h@.subrange(a as int, b as int)),
            None => bearer_spec(h@) is None,
        },
))]
#[must_use]
pub fn bearer(h: &[u8]) -> Option<(usize, usize)> {
    if starts_with(h, word_bytes(Word::BearerUpper)) || starts_with(h, word_bytes(Word::BearerLower)) {
        proof! { assert(h@.subrange(7, h.len() as int) =~= h@.skip(7)); }
        Some(trim_in(h, 7, h.len()))
    } else {
        None
    }
}

/// The first address in an `X-Forwarded-For` value, as a range of `v`: the
/// text before the first `,`, trimmed.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r.0 <= r.1 <= v.len(),
        v@.subrange(r.0 as int, r.1 as int) == trimmed(v@.subrange(0, find(v@, 0, v@.len() as int, 44))),
))]
#[must_use]
pub fn forwarded(v: &[u8]) -> (usize, usize) {
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= v.len(),
            find(v@, 0, v@.len() as int, 44) == find(v@, i as int, v@.len() as int, 44),
        decreases v.len() - i
    ))]
    while i < v.len() && v[i] != 44 {
        i += 1;
    }
    trim_in(v, 0, i)
}

/// The page size from the `limit` query parameter: [`page_limit_spec`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r == page_limit_spec(match limit { Some(t) => Some(t@), None => None }),
))]
#[must_use]
pub fn page_limit(limit: Option<&[u8]>) -> Option<u32> {
    let n: u64 = match limit {
        None => 50,
        Some(t) => match parse_u64(t) {
            Some(n) => n,
            None => 0,
        },
    };
    if 1 <= n && n <= 200 { Some(n as u32) } else { None }
}

/// Whether a page of `len` items, asked for `limit`, may have more after it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (len == limit as usize)))]
#[must_use]
pub const fn more_pages(len: usize, limit: u32) -> bool {
    len == limit as usize
}

/// The `include_descendants` flag: [`flag_spec`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r == flag_spec(match v { Some(t) => Some(t@), None => None }),
))]
#[must_use]
pub fn flag(v: Option<&[u8]>) -> Option<bool> {
    match v {
        None => Some(false),
        Some(t) => {
            if is(t, Word::True) {
                Some(true)
            } else if is(t, Word::False) {
                Some(false)
            } else {
                None
            }
        }
    }
}

/// Whether JSON bodies may be read under the content type `ct`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == json_type_spec(ct@)))]
#[must_use]
pub fn json_type(ct: &[u8]) -> bool {
    starts_with(ct, word_bytes(Word::Json)) || starts_with(ct, word_bytes(Word::MergePatch))
}

/// Whether a body of `n` bytes is within [`MAX_BODY`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == (n <= MAX_BODY)))]
#[must_use]
pub const fn body_fits(n: usize) -> bool {
    n <= MAX_BODY
}

/// When a passkey session started at `now` ends: [`SESSION_MS`] later,
/// saturating at the end of time.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r as int == if now + SESSION_MS <= i64::MAX { now + SESSION_MS } else { i64::MAX as int },
))]
#[must_use]
pub const fn session_expiry(now: i64) -> i64 {
    if now <= i64::MAX - SESSION_MS { now + SESSION_MS } else { i64::MAX }
}

/// Why a character's own fields are refused, in the order they are checked.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CharacterRefusal {
    /// `character_exp_rate` is outside `[0, 100%)`.
    ExpRate,
    /// `character_exp` does not fit an `i64` (SQLite's integer).
    ExpTooLarge,
    /// `character_guild_name` is over 32 characters.
    GuildTooLong,
    /// `character_image` is over 4096 characters.
    ImageTooLong,
    /// `notes` is over 4000 characters.
    NotesTooLong,
    /// `character_image` is not an `https://` URL.
    ImageNotHttps,
}

/// Why an account's fields are refused, in the order they are checked.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AccountRefusal {
    /// `label` is over 100 characters.
    LabelTooLong,
    /// `notes` is over 4000 characters.
    NotesTooLong,
}

#[cfg(feature = "verus")]
verus! {

/// An optional byte slice's contents.
pub open spec fn opt(v: Option<&[u8]>) -> Option<Seq<u8>> {
    match v {
        Some(t) => Some(t@),
        None => None,
    }
}

/// An optional text is absent or at most `max` characters.
pub open spec fn fits(t: Option<Seq<u8>>, max: nat) -> bool {
    match t {
        Some(t) => chars(t) <= max,
        None => true,
    }
}

/// The checks on a character's own fields, in order; on success, the
/// experience as SQLite stores it.
pub open spec fn character_spec(
    exp_rate: Option<i64>,
    exp: Option<u64>,
    guild: Option<Seq<u8>>,
    image: Option<Seq<u8>>,
    notes: Option<Seq<u8>>,
) -> Result<Option<i64>, CharacterRefusal> {
    if exp_rate matches Some(r) && !(0 <= r < 100_000) {
        Err(CharacterRefusal::ExpRate)
    } else if exp matches Some(e) && e > i64::MAX {
        Err(CharacterRefusal::ExpTooLarge)
    } else if !fits(guild, 32) {
        Err(CharacterRefusal::GuildTooLong)
    } else if !fits(image, 4096) {
        Err(CharacterRefusal::ImageTooLong)
    } else if !fits(notes, 4000) {
        Err(CharacterRefusal::NotesTooLong)
    } else if image matches Some(u) && !has_prefix(u, word(Word::Https)) {
        Err(CharacterRefusal::ImageNotHttps)
    } else {
        Ok(match exp {
            Some(e) => Some(e as i64),
            None => None,
        })
    }
}

/// The checks on an account's own fields, in order.
pub open spec fn account_spec(label: Option<Seq<u8>>, notes: Option<Seq<u8>>) -> Result<(), AccountRefusal> {
    if !fits(label, 100) {
        Err(AccountRefusal::LabelTooLong)
    } else if !fits(notes, 4000) {
        Err(AccountRefusal::NotesTooLong)
    } else {
        Ok(())
    }
}

} // verus!

/// Whether an optional text is absent or at most `max` characters.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == fits(opt(t), max as nat)))]
#[must_use]
pub fn text_fits(t: Option<&[u8]>, max: usize) -> bool {
    match t {
        Some(t) => char_count(t) <= max,
        None => true,
    }
}

/// Checks a character's own fields (the world, class and name are looked up
/// first): [`character_spec`]. On success, the experience as SQLite stores it.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures r == character_spec(exp_rate, exp, opt(guild), opt(image), opt(notes)),
))]
#[allow(clippy::collapsible_if, reason = "Verus does not take let chains")]
pub fn character_fields(
    exp_rate: Option<i64>,
    exp: Option<u64>,
    guild: Option<&[u8]>,
    image: Option<&[u8]>,
    notes: Option<&[u8]>,
) -> Result<Option<i64>, CharacterRefusal> {
    if let Some(r) = exp_rate {
        if !crate::rules::exp_rate_ok(r) {
            return Err(CharacterRefusal::ExpRate);
        }
    }
    let stored = match exp {
        Some(e) => {
            if e > i64::MAX as u64 {
                return Err(CharacterRefusal::ExpTooLarge);
            }
            Some(e as i64)
        }
        None => None,
    };
    if !text_fits(guild, 32) {
        return Err(CharacterRefusal::GuildTooLong);
    }
    if !text_fits(image, 4096) {
        return Err(CharacterRefusal::ImageTooLong);
    }
    if !text_fits(notes, 4000) {
        return Err(CharacterRefusal::NotesTooLong);
    }
    if let Some(u) = image {
        if !starts_with(u, word_bytes(Word::Https)) {
            return Err(CharacterRefusal::ImageNotHttps);
        }
    }
    Ok(stored)
}

/// Checks an account's own fields (the region is checked first):
/// [`account_spec`].
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r => ensures r == account_spec(opt(label), opt(notes))))]
pub fn account_fields(label: Option<&[u8]>, notes: Option<&[u8]>) -> Result<(), AccountRefusal> {
    if !text_fits(label, 100) {
        return Err(AccountRefusal::LabelTooLong);
    }
    if !text_fits(notes, 4000) {
        return Err(AccountRefusal::NotesTooLong);
    }
    Ok(())
}

/// A required name (a token label, a display name): the range of `s` left
/// after trimming, if that is `min..=max` characters.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        match r {
            Some((a, b)) => a <= b <= s.len() && s@.subrange(a as int, b as int) == trimmed(s@)
                && min <= chars(trimmed(s@)) <= max,
            None => !(min <= chars(trimmed(s@)) <= max),
        },
))]
#[must_use]
pub fn name_in(s: &[u8], min: usize, max: usize) -> Option<(usize, usize)> {
    let (a, b) = crate::text::trim(s);
    let n = crate::text::char_count_in(s, a, b);
    if min <= n && n <= max { Some((a, b)) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(m: Method, path: &str) -> Routed {
        let segs: Vec<&[u8]> = path.split('/').filter(|s| !s.is_empty()).map(str::as_bytes).collect();
        route(m, &segs)
    }

    /// Every word, kept complete by the exhaustive match below.
    const ALL_WORDS: [Word; 62] = [
        Word::V1,
        Word::Me,
        Word::Tokens,
        Word::Audit,
        Word::Accounts,
        Word::Characters,
        Word::Stat,
        Word::History,
        Word::Health,
        Word::Docs,
        Word::Ref,
        Word::Regions,
        Word::Worlds,
        Word::Classes,
        Word::Auth,
        Word::Passkey,
        Word::Register,
        Word::Login,
        Word::Start,
        Word::Finish,
        Word::ItemEquipment,
        Word::Sheet,
        Word::SymbolEquipment,
        Word::HyperStat,
        Word::Ability,
        Word::LinkSkill,
        Word::Vmatrix,
        Word::Hexamatrix,
        Word::Get,
        Word::Head,
        Word::Post,
        Word::Put,
        Word::Patch,
        Word::Delete,
        Word::Other,
        Word::MeRead,
        Word::TokenRead,
        Word::TokenMint,
        Word::TokenRevoke,
        Word::AuditRead,
        Word::AccountRead,
        Word::AccountCreate,
        Word::AccountUpdate,
        Word::AccountDelete,
        Word::CharacterRead,
        Word::CharacterCreate,
        Word::CharacterUpdate,
        Word::CharacterDelete,
        Word::StatRead,
        Word::StatReplace,
        Word::StatUpdate,
        Word::EquipmentRead,
        Word::EquipmentReplace,
        Word::UserCreate,
        Word::SessionCreate,
        Word::Json,
        Word::MergePatch,
        Word::BearerUpper,
        Word::BearerLower,
        Word::Https,
        Word::True,
        Word::False,
    ];

    #[test]
    fn every_word_is_ascii() {
        for w in ALL_WORDS {
            match w {
                Word::V1
                | Word::Me
                | Word::Tokens
                | Word::Audit
                | Word::Accounts
                | Word::Characters
                | Word::Stat
                | Word::History
                | Word::Health
                | Word::Docs
                | Word::Ref
                | Word::Regions
                | Word::Worlds
                | Word::Classes
                | Word::Auth
                | Word::Passkey
                | Word::Register
                | Word::Login
                | Word::Start
                | Word::Finish
                | Word::ItemEquipment
                | Word::Sheet
                | Word::SymbolEquipment
                | Word::HyperStat
                | Word::Ability
                | Word::LinkSkill
                | Word::Vmatrix
                | Word::Hexamatrix
                | Word::Get
                | Word::Head
                | Word::Post
                | Word::Put
                | Word::Patch
                | Word::Delete
                | Word::Other
                | Word::MeRead
                | Word::TokenRead
                | Word::TokenMint
                | Word::TokenRevoke
                | Word::AuditRead
                | Word::AccountRead
                | Word::AccountCreate
                | Word::AccountUpdate
                | Word::AccountDelete
                | Word::CharacterRead
                | Word::CharacterCreate
                | Word::CharacterUpdate
                | Word::CharacterDelete
                | Word::StatRead
                | Word::StatReplace
                | Word::StatUpdate
                | Word::EquipmentRead
                | Word::EquipmentReplace
                | Word::UserCreate
                | Word::SessionCreate
                | Word::Json
                | Word::MergePatch
                | Word::BearerUpper
                | Word::BearerLower
                | Word::Https
                | Word::True
                | Word::False => {}
            }
            assert!(word_bytes(w).is_ascii(), "{w:?}");
        }
    }

    #[test]
    fn words_are_their_names() {
        for (w, s) in [
            (Word::V1, "v1"),
            (Word::HyperStat, "hyper-stat"),
            (Word::MergePatch, "application/merge-patch+json"),
            (Word::BearerLower, "bearer "),
        ] {
            assert_eq!(word_bytes(w), s.as_bytes());
        }
    }

    #[test]
    fn routes() {
        assert_eq!(r(Method::Patch, "/v1/characters/chr_x"), Routed::Found(Route::UpdateCharacter));
        assert_eq!(r(Method::Get, "/v1/characters/chr_x/hyper-stat"), Routed::Found(Route::Planned(1)));
        assert_eq!(r(Method::Put, "/v1/characters/chr_x/item-equipment"), Routed::Found(Route::ReplaceItemEquipment));
        assert_eq!(r(Method::Get, "/v1/characters/chr_x/sheet"), Routed::Found(Route::CharacterSheet));
        assert_eq!(r(Method::Put, "/v1/characters/chr_x/sheet"), Routed::NotAllowed);
        assert_eq!(
            r(Method::Get, "/v1/characters/chr_x/item-equipment/history"),
            Routed::Found(Route::ItemEquipmentHistory)
        );
        assert_eq!(r(Method::Patch, "/v1/characters/chr_x/item-equipment"), Routed::NotAllowed);
        assert_eq!(r(Method::Put, "/v1/characters"), Routed::NotAllowed);
        assert_eq!(r(Method::Get, "/v1/nope"), Routed::NotFound);
        assert_eq!(r(Method::Get, "/v1/characters/chr_x/nope"), Routed::NotFound);
        assert_eq!(r(Method::Get, "/health"), Routed::Found(Route::Health));
        assert_eq!(r(Method::Post, "/health"), Routed::NotAllowed);
        assert_eq!(r(Method::Get, "/v1/auth/passkey/anything"), Routed::NotAllowed);
        assert_eq!(r(Method::Post, "/v1/auth/passkey/anything"), Routed::NotFound);
        assert_eq!(r(Method::Post, "/v1/auth/passkey/login/finish"), Routed::Found(Route::LoginFinish));
        assert_eq!(r(Method::Get, "//v1//me/"), Routed::Found(Route::Me));
    }

    #[test]
    fn headers_and_params() {
        let h = b"Bearer  msk_abc \t";
        assert_eq!(bearer(h).map(|(a, b)| &h[a..b]), Some(&b"msk_abc"[..]));
        assert_eq!(bearer(b"Basic x"), None);
        let v = b" 1.2.3.4 , 5.6.7.8";
        let (a, b) = forwarded(v);
        assert_eq!(&v[a..b], b"1.2.3.4");
        assert_eq!(page_limit(None), Some(50));
        assert_eq!(page_limit(Some(b"200")), Some(200));
        assert_eq!(page_limit(Some(b"201")), None);
        assert_eq!(page_limit(Some(b"x")), None);
        assert_eq!(flag(Some(b"true")), Some(true));
        assert_eq!(flag(Some(b"yes")), None);
        assert!(json_type(b"application/json; charset=utf-8"));
        assert!(!json_type(b"text/plain"));
        assert_eq!(Method::parse(b"HEAD"), Method::Get);
        assert_eq!(Method::parse(b"get"), Method::Other);
        assert_eq!(session_expiry(i64::MAX - 1), i64::MAX);
    }
}
