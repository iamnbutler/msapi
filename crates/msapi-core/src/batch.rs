//! The durable write log's byte formats, with no I/O.
//!
//! A batch is the statements of one committed transaction, back to back. Each
//! statement is its SQL (a u32 length, then the bytes), the parameter count
//! (u32), then each parameter as a tag byte and its value. Integers and reals
//! (as their bits) are 8 bytes; text and blobs are a u32 length and the bytes.
//! Every number is big-endian.
//!
//! The log's state is a run of frames: a u64 sequence number, a u64 body
//! length, then the body.
//!
//! Verus checks that decoding never reads out of bounds, that whatever it
//! accepts re-encodes to exactly its input, and that it gives back every
//! statement list that was encoded.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_lossless,
    reason = "plain casts are what Verus checks; each is proven in range or a deliberate two's-complement reinterpretation"
)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

/// Parameter tag: SQL `NULL`.
#[cfg_attr(feature = "verus", verus_verify)]
pub const NULL: u8 = 0;
/// Parameter tag: a 64-bit integer.
#[cfg_attr(feature = "verus", verus_verify)]
pub const INTEGER: u8 = 1;
/// Parameter tag: a 64-bit float, as its bits.
#[cfg_attr(feature = "verus", verus_verify)]
pub const REAL: u8 = 2;
/// Parameter tag: text, as bytes.
#[cfg_attr(feature = "verus", verus_verify)]
pub const TEXT: u8 = 3;
/// Parameter tag: a blob.
#[cfg_attr(feature = "verus", verus_verify)]
pub const BLOB: u8 = 4;

/// A statement parameter.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub enum Param {
    /// SQL `NULL`.
    Null,
    /// An integer.
    Integer(i64),
    /// A float, as its bits (`f64::to_bits`).
    Real(u64),
    /// Text, as bytes. The format does not check it is UTF-8.
    Text(Vec<u8>),
    /// A blob.
    Blob(Vec<u8>),
}

/// A statement and its parameters.
#[cfg_attr(feature = "verus", verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub struct Statement {
    /// The SQL, as bytes.
    pub sql: Vec<u8>,
    /// The parameters, in order.
    pub params: Vec<Param>,
}

#[cfg(feature = "verus")]
#[allow(missing_docs, reason = "Verus generates undocumented accessors for spec enums")]
mod view {
    use vstd::prelude::*;

    verus! {

    /// What a [`super::Param`] means, for specs.
    pub enum ParamView {
        /// SQL `NULL`.
        Null,
        /// An integer.
        Integer(i64),
        /// A float's bits.
        Real(u64),
        /// Text bytes.
        Text(Seq<u8>),
        /// Blob bytes.
        Blob(Seq<u8>),
    }

    } // verus!
}

#[cfg(feature = "verus")]
pub use view::ParamView;

#[cfg(feature = "verus")]
verus! {

/// What a [`Statement`] means, for specs.
pub struct StatementView {
    /// The SQL bytes.
    pub sql: Seq<u8>,
    /// The parameters.
    pub params: Seq<ParamView>,
}

impl View for Param {
    type V = ParamView;

    open spec fn view(&self) -> ParamView {
        match self {
            Param::Null => ParamView::Null,
            Param::Integer(i) => ParamView::Integer(*i),
            Param::Real(r) => ParamView::Real(*r),
            Param::Text(t) => ParamView::Text(t@),
            Param::Blob(b) => ParamView::Blob(b@),
        }
    }
}

/// Each parameter's view.
pub open spec fn params_view(ps: Seq<Param>) -> Seq<ParamView> {
    ps.map_values(|p: Param| p@)
}

impl View for Statement {
    type V = StatementView;

    open spec fn view(&self) -> StatementView {
        StatementView { sql: self.sql@, params: params_view(self.params@) }
    }
}

/// Each statement's view.
pub open spec fn statements_view(ss: Seq<Statement>) -> Seq<StatementView> {
    ss.map_values(|s: Statement| s@)
}

/// `n` as four big-endian bytes.
pub open spec fn be4(n: u32) -> Seq<u8> {
    seq![(n >> 24) as u8, (n >> 16) as u8, (n >> 8) as u8, n as u8]
}

/// `n` as eight big-endian bytes.
pub open spec fn be8(n: u64) -> Seq<u8> {
    seq![
        (n >> 56) as u8, (n >> 48) as u8, (n >> 40) as u8, (n >> 32) as u8,
        (n >> 24) as u8, (n >> 16) as u8, (n >> 8) as u8, n as u8,
    ]
}

/// A u32 length, then the bytes.
pub open spec fn enc_bytes(b: Seq<u8>) -> Seq<u8> {
    be4(b.len() as u32) + b
}

/// A parameter: its tag, then its value.
pub open spec fn enc_param(p: ParamView) -> Seq<u8> {
    match p {
        ParamView::Null => seq![NULL],
        ParamView::Integer(i) => seq![INTEGER] + be8(i as u64),
        ParamView::Real(r) => seq![REAL] + be8(r),
        ParamView::Text(t) => seq![TEXT] + enc_bytes(t),
        ParamView::Blob(b) => seq![BLOB] + enc_bytes(b),
    }
}

/// Whether a parameter's length fits the format's u32.
pub open spec fn param_fits(p: ParamView) -> bool {
    match p {
        ParamView::Text(t) => t.len() <= u32::MAX,
        ParamView::Blob(b) => b.len() <= u32::MAX,
        _ => true,
    }
}

/// Parameters, back to back.
pub open spec fn enc_params(ps: Seq<ParamView>) -> Seq<u8>
    decreases ps.len(),
{
    if ps.len() == 0 { Seq::empty() } else { enc_params(ps.drop_last()) + enc_param(ps.last()) }
}

/// Whether every length in a statement fits the format's u32.
pub open spec fn statement_fits(s: StatementView) -> bool {
    &&& s.sql.len() <= u32::MAX
    &&& s.params.len() <= u32::MAX
    &&& forall|k: int| 0 <= k < s.params.len() ==> #[trigger] param_fits(s.params[k])
}

/// A statement: its SQL, the parameter count, then the parameters.
pub open spec fn enc_statement(s: StatementView) -> Seq<u8> {
    enc_bytes(s.sql) + be4(s.params.len() as u32) + enc_params(s.params)
}

/// Whether every statement fits.
pub open spec fn batch_fits(ss: Seq<StatementView>) -> bool {
    forall|k: int| 0 <= k < ss.len() ==> #[trigger] statement_fits(ss[k])
}

/// A batch: its statements' encodings, back to back.
pub open spec fn enc_batch(ss: Seq<StatementView>) -> Seq<u8>
    decreases ss.len(),
{
    if ss.len() == 0 { Seq::empty() } else { enc_batch(ss.drop_last()) + enc_statement(ss.last()) }
}

/// A frame of the log's state.
pub open spec fn enc_frame(seq: u64, body: Seq<u8>) -> Seq<u8> {
    be8(seq) + be8(body.len() as u64) + body
}

/// `e` sits at `data[at..]`.
pub open spec fn encoded_at(data: Seq<u8>, at: int, e: Seq<u8>) -> bool {
    0 <= at && at + e.len() <= data.len() && data.subrange(at, at + e.len()) == e
}

/// A parameter's tag byte.
pub open spec fn tag_of(p: ParamView) -> u8 {
    match p {
        ParamView::Null => NULL,
        ParamView::Integer(_) => INTEGER,
        ParamView::Real(_) => REAL,
        ParamView::Text(_) => TEXT,
        ParamView::Blob(_) => BLOB,
    }
}

proof fn lemma_be4_bytes(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        ((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 24u32) as u8 == b0,
        ((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 16u32) as u8 == b1,
        ((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 8u32) as u8 == b2,
        (((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) as u8 == b3,
{
    assert(((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 24u32) as u8 == b0 && ((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 16u32) as u8 == b1 && ((((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) >> 8u32) as u8 == b2 && (((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (b3 as u32)) as u8 == b3) by (bit_vector);
}

proof fn lemma_be4_value(n: u32)
    ensures
        n == ((((n >> 24u32) as u8) as u32) << 24u32) | ((((n >> 16u32) as u8) as u32) << 16u32)
            | ((((n >> 8u32) as u8) as u32) << 8u32) | ((n as u8) as u32),
{
    assert(n == ((((n >> 24u32) as u8) as u32) << 24u32) | ((((n >> 16u32) as u8) as u32) << 16u32) | ((((n >> 8u32) as u8) as u32) << 8u32) | ((n as u8) as u32)) by (bit_vector);
}

/// Eight big-endian bytes as a number.
pub open spec fn join8(b: Seq<u8>) -> u64 {
    ((b[0] as u64) << 56u64) | ((b[1] as u64) << 48u64) | ((b[2] as u64) << 40u64) | ((b[3] as u64) << 32u64)
        | ((b[4] as u64) << 24u64) | ((b[5] as u64) << 16u64) | ((b[6] as u64) << 8u64) | (b[7] as u64)
}

proof fn lemma_be8_bytes(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8, n: u64)
    requires
        n == ((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64)
            | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64),
    ensures
        (n >> 56u64) as u8 == b0, (n >> 48u64) as u8 == b1, (n >> 40u64) as u8 == b2, (n >> 32u64) as u8 == b3,
        (n >> 24u64) as u8 == b4, (n >> 16u64) as u8 == b5, (n >> 8u64) as u8 == b6, n as u8 == b7,
{
    assert((n >> 56u64) as u8 == b0 && (n >> 48u64) as u8 == b1 && (n >> 40u64) as u8 == b2 && (n >> 32u64) as u8 == b3 && (n >> 24u64) as u8 == b4 && (n >> 16u64) as u8 == b5 && (n >> 8u64) as u8 == b6 && n as u8 == b7) by (bit_vector) requires n == ((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((b3 as u64) << 32u64)
            | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64) << 8u64) | (b7 as u64);
}

proof fn lemma_be8_value(n: u64)
    ensures
        n == ((((n >> 56u64) as u8) as u64) << 56u64) | ((((n >> 48u64) as u8) as u64) << 48u64)
            | ((((n >> 40u64) as u8) as u64) << 40u64) | ((((n >> 32u64) as u8) as u64) << 32u64)
            | ((((n >> 24u64) as u8) as u64) << 24u64) | ((((n >> 16u64) as u8) as u64) << 16u64)
            | ((((n >> 8u64) as u8) as u64) << 8u64) | ((n as u8) as u64),
{
    assert(n == ((((n >> 56u64) as u8) as u64) << 56u64) | ((((n >> 48u64) as u8) as u64) << 48u64) | ((((n >> 40u64) as u8) as u64) << 40u64) | ((((n >> 32u64) as u8) as u64) << 32u64) | ((((n >> 24u64) as u8) as u64) << 24u64) | ((((n >> 16u64) as u8) as u64) << 16u64) | ((((n >> 8u64) as u8) as u64) << 8u64) | ((n as u8) as u64)) by (bit_vector);
}

proof fn lemma_be8_join(n: u64)
    ensures join8(be8(n)) == n,
{
    lemma_be8_value(n);
}

proof fn lemma_cast(i: i64, w: u64)
    ensures (w as i64) as u64 == w, (i as u64) as i64 == i,
{
    assert((w as i64) as u64 == w) by (bit_vector);
    assert((i as u64) as i64 == i) by (bit_vector);
}

/// A piece of what sits at `at` sits at `at + off`.
proof fn lemma_sub(data: Seq<u8>, at: int, whole: Seq<u8>, off: int, part: Seq<u8>)
    requires
        encoded_at(data, at, whole),
        0 <= off,
        off + part.len() <= whole.len(),
        whole.subrange(off, off + part.len()) == part,
    ensures
        encoded_at(data, at + off, part),
{
    assert forall|j: int| 0 <= j < part.len() implies data.subrange(at + off, at + off + part.len())[j] == part[j] by {
        assert(data.subrange(at, at + whole.len())[off + j] == whole[off + j]);
        assert(whole.subrange(off, off + part.len())[j] == whole[off + j]);
    }
    assert(data.subrange(at + off, at + off + part.len()) =~= part);
}

/// `a + b` sits at `at` exactly when `a` does and `b` follows it.
proof fn lemma_split(data: Seq<u8>, at: int, a: Seq<u8>, b: Seq<u8>)
    requires
        encoded_at(data, at, a + b),
    ensures
        encoded_at(data, at, a),
        encoded_at(data, at + a.len(), b),
{
    lemma_sub(data, at, a + b, 0, a);
    assert((a + b).subrange(0, a.len() as int) =~= a);
    assert((a + b).subrange(a.len() as int, (a.len() + b.len()) as int) =~= b);
    lemma_sub(data, at, a + b, a.len() as int, b);
}

proof fn lemma_join(data: Seq<u8>, at: int, a: Seq<u8>, b: Seq<u8>)
    requires
        encoded_at(data, at, a),
        encoded_at(data, at + a.len(), b),
    ensures
        encoded_at(data, at, a + b),
{
    assert forall|j: int| 0 <= j < a.len() + b.len() implies data.subrange(at, at + a.len() + b.len())[j] == (a + b)[j] by {
        if j < a.len() {
            assert(data.subrange(at, at + a.len())[j] == a[j]);
        } else {
            assert(data.subrange(at + a.len(), at + a.len() + b.len())[j - a.len()] == b[j - a.len()]);
        }
    }
    assert(data.subrange(at, at + (a + b).len()) =~= a + b);
}

proof fn lemma_param_tag(data: Seq<u8>, at: int, q: ParamView)
    requires
        encoded_at(data, at, enc_param(q)),
    ensures
        at < data.len(),
        data[at] == tag_of(q),
        enc_param(q) == seq![tag_of(q)] + enc_param(q).subrange(1, enc_param(q).len() as int),
{
    assert(enc_param(q)[0] == tag_of(q));
    assert(data.subrange(at, at + enc_param(q).len())[0] == data[at]);
    assert(enc_param(q) =~= seq![tag_of(q)] + enc_param(q).subrange(1, enc_param(q).len() as int));
}

proof fn lemma_params_prefix(ps: Seq<ParamView>, k: int)
    requires
        0 <= k <= ps.len(),
    ensures
        enc_params(ps.take(k)).len() <= enc_params(ps).len(),
        enc_params(ps).subrange(0, enc_params(ps.take(k)).len() as int) == enc_params(ps.take(k)),
    decreases ps.len(),
{
    if k == ps.len() {
        assert(ps.take(k) =~= ps);
        assert(enc_params(ps).subrange(0, enc_params(ps).len() as int) =~= enc_params(ps));
    } else {
        lemma_params_prefix(ps.drop_last(), k);
        assert(ps.drop_last().take(k) =~= ps.take(k));
        let l = enc_params(ps.take(k)).len() as int;
        assert(enc_params(ps).subrange(0, l) =~= enc_params(ps.drop_last()).subrange(0, l));
    }
}

proof fn lemma_params_step(ps: Seq<ParamView>, k: int)
    requires
        0 <= k < ps.len(),
    ensures
        enc_params(ps.take(k + 1)) == enc_params(ps.take(k)) + enc_param(ps[k]),
{
    assert(ps.take(k + 1).drop_last() =~= ps.take(k));
}

/// The `k`th parameter of an encoded list sits right after the ones before it.
proof fn lemma_param_in_list(data: Seq<u8>, at: int, ps: Seq<ParamView>, k: int)
    requires
        encoded_at(data, at, enc_params(ps)),
        0 <= k < ps.len(),
    ensures
        encoded_at(data, at + enc_params(ps.take(k)).len(), enc_param(ps[k])),
{
    lemma_params_prefix(ps, k + 1);
    lemma_sub(data, at, enc_params(ps), 0, enc_params(ps.take(k + 1)));
    lemma_params_step(ps, k);
    lemma_split(data, at, enc_params(ps.take(k)), enc_param(ps[k]));
}

proof fn lemma_batch_prefix(ss: Seq<StatementView>, k: int)
    requires
        0 <= k <= ss.len(),
    ensures
        enc_batch(ss.take(k)).len() <= enc_batch(ss).len(),
        k < ss.len() ==> enc_batch(ss.take(k)).len() < enc_batch(ss).len(),
        enc_batch(ss).subrange(0, enc_batch(ss.take(k)).len() as int) == enc_batch(ss.take(k)),
    decreases ss.len(),
{
    if k == ss.len() {
        assert(ss.take(k) =~= ss);
        assert(enc_batch(ss).subrange(0, enc_batch(ss).len() as int) =~= enc_batch(ss));
    } else {
        lemma_batch_prefix(ss.drop_last(), k);
        assert(ss.drop_last().take(k) =~= ss.take(k));
        let l = enc_batch(ss.take(k)).len() as int;
        assert(enc_batch(ss).subrange(0, l) =~= enc_batch(ss.drop_last()).subrange(0, l));
    }
}

proof fn lemma_statement_in_batch(data: Seq<u8>, ss: Seq<StatementView>, k: int)
    requires
        data == enc_batch(ss),
        0 <= k < ss.len(),
    ensures
        encoded_at(data, enc_batch(ss.take(k)).len() as int, enc_statement(ss[k])),
{
    lemma_batch_prefix(ss, k + 1);
    assert(ss.take(k + 1).drop_last() =~= ss.take(k));
    assert(data.subrange(0, data.len() as int) =~= data);
    lemma_sub(data, 0, data, 0, enc_batch(ss.take(k + 1)));
    lemma_split(data, 0, enc_batch(ss.take(k)), enc_statement(ss[k]));
}

/// The pieces of an encoded statement.
proof fn lemma_statement_parts(data: Seq<u8>, at: int, q: StatementView)
    requires
        encoded_at(data, at, enc_statement(q)),
    ensures
        encoded_at(data, at, be4(q.sql.len() as u32)),
        encoded_at(data, at + 4, q.sql),
        encoded_at(data, at + 4 + q.sql.len(), be4(q.params.len() as u32)),
        encoded_at(data, at + 8 + q.sql.len(), enc_params(q.params)),
        enc_statement(q).len() == 8 + q.sql.len() + enc_params(q.params).len(),
{
    let a = be4(q.sql.len() as u32);
    let c = be4(q.params.len() as u32);
    assert(enc_statement(q) =~= a + (q.sql + (c + enc_params(q.params))));
    lemma_split(data, at, a, q.sql + (c + enc_params(q.params)));
    lemma_split(data, at + 4, q.sql, c + enc_params(q.params));
    lemma_split(data, at + 4 + q.sql.len(), c, enc_params(q.params));
}

} // verus!

/// Appends `n`, big-endian.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(
    ensures final(out)@ == old(out)@ + be4(n),
))]
fn put_u32(out: &mut Vec<u8>, n: u32) {
    out.push((n >> 24) as u8);
    out.push((n >> 16) as u8);
    out.push((n >> 8) as u8);
    out.push(n as u8);
    proof! { assert(out@ =~= old(out)@ + be4(n)); }
}

/// Appends `n`, big-endian.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(
    ensures final(out)@ == old(out)@ + be8(n),
))]
fn put_u64(out: &mut Vec<u8>, n: u64) {
    out.push((n >> 56) as u8);
    out.push((n >> 48) as u8);
    out.push((n >> 40) as u8);
    out.push((n >> 32) as u8);
    out.push((n >> 24) as u8);
    out.push((n >> 16) as u8);
    out.push((n >> 8) as u8);
    out.push(n as u8);
    proof! { assert(out@ =~= old(out)@ + be8(n)); }
}

/// Appends `b`'s length and then `b`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(
    requires b@.len() <= u32::MAX,
    ensures final(out)@ == old(out)@ + enc_bytes(b@),
))]
fn put_bytes(out: &mut Vec<u8>, b: &[u8]) {
    put_u32(out, b.len() as u32);
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= b.len(),
            out@ == old(out)@ + be4(b@.len() as u32) + b@.subrange(0, i as int),
        decreases b.len() - i
    ))]
    while i < b.len() {
        out.push(b[i]);
        proof! { assert(b@.subrange(0, i + 1) =~= b@.subrange(0, i as int).push(b@[i as int])); }
        i += 1;
    }
    proof! { assert(b@.subrange(0, b@.len() as int) =~= b@); }
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(
    requires param_fits(p@),
    ensures final(out)@ == old(out)@ + enc_param(p@),
))]
fn put_param(out: &mut Vec<u8>, p: &Param) {
    match p {
        Param::Null => out.push(NULL),
        Param::Integer(i) => {
            out.push(INTEGER);
            put_u64(out, *i as u64);
        }
        Param::Real(r) => {
            out.push(REAL);
            put_u64(out, *r);
        }
        Param::Text(t) => {
            out.push(TEXT);
            put_bytes(out, t.as_slice());
        }
        Param::Blob(b) => {
            out.push(BLOB);
            put_bytes(out, b.as_slice());
        }
    }
    proof! { assert(out@ =~= old(out)@ + enc_param(p@)); }
}

/// Appends `s` to the batch `out`. Returns `false`, appending nothing, if the
/// SQL, the parameter count or a parameter is too long for its u32 length.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r == statement_fits(s@),
        r ==> final(out)@ == old(out)@ + enc_statement(s@),
        !r ==> final(out)@ == old(out)@,
))]
pub fn encode_statement(out: &mut Vec<u8>, s: &Statement) -> bool {
    if s.sql.len() > u32::MAX as usize || s.params.len() > u32::MAX as usize {
        return false;
    }
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s.params.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] param_fits(s.params@[k]@),
        decreases s.params.len() - i
    ))]
    while i < s.params.len() {
        let long = match &s.params[i] {
            Param::Text(b) | Param::Blob(b) => b.len() > u32::MAX as usize,
            _ => false,
        };
        if long {
            proof! { assert(!param_fits(s@.params[i as int])); }
            return false;
        }
        i += 1;
    }
    proof! { assert(statement_fits(s@)); }

    put_bytes(out, s.sql.as_slice());
    put_u32(out, s.params.len() as u32);
    let mut i: usize = 0;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            i <= s.params.len(),
            statement_fits(s@),
            out@ == old(out)@ + enc_bytes(s.sql@) + be4(s.params@.len() as u32) + enc_params(s@.params.take(i as int)),
        decreases s.params.len() - i
    ))]
    while i < s.params.len() {
        proof! {
            assert(param_fits(s@.params[i as int]));
            assert(s@.params.take(i + 1).drop_last() =~= s@.params.take(i as int));
        }
        put_param(out, &s.params[i]);
        i += 1;
    }
    proof! {
        assert(s@.params.take(i as int) =~= s@.params);
        assert(out@ =~= old(out)@ + enc_statement(s@));
    }
    true
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires at + 4 <= data@.len(),
    ensures
        be4(r) == data@.subrange(at as int, at + 4),
        forall|n: u32| be4(n) == data@.subrange(at as int, at + 4) ==> n == r,
))]
fn read_u32(data: &[u8], at: usize) -> u32 {
    let r = ((data[at] as u32) << 24)
        | ((data[at + 1] as u32) << 16)
        | ((data[at + 2] as u32) << 8)
        | (data[at + 3] as u32);
    proof! {
        lemma_be4_bytes(data@[at as int], data@[at + 1], data@[at + 2], data@[at + 3]);
        assert(be4(r) =~= data@.subrange(at as int, at + 4));
        assert forall|n: u32| be4(n) == data@.subrange(at as int, at + 4) implies n == r by {
            lemma_be4_value(n);
            assert(be4(n)[0] == data@[at as int] && be4(n)[1] == data@[at + 1]);
            assert(be4(n)[2] == data@[at + 2] && be4(n)[3] == data@[at + 3]);
        }
    }
    r
}

#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires at + 8 <= data@.len(),
    ensures
        be8(r) == data@.subrange(at as int, at + 8),
        forall|n: u64| be8(n) == data@.subrange(at as int, at + 8) ==> n == r,
))]
fn read_u64(data: &[u8], at: usize) -> u64 {
    let r = ((data[at] as u64) << 56)
        | ((data[at + 1] as u64) << 48)
        | ((data[at + 2] as u64) << 40)
        | ((data[at + 3] as u64) << 32)
        | ((data[at + 4] as u64) << 24)
        | ((data[at + 5] as u64) << 16)
        | ((data[at + 6] as u64) << 8)
        | (data[at + 7] as u64);
    proof! {
        let b = data@.subrange(at as int, at + 8);
        assert(r == join8(b));
        lemma_be8_bytes(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], r);
        assert(be8(r) =~= b);
        assert forall|n: u64| be8(n) == b implies n == r by {
            lemma_be8_join(n);
        }
    }
    r
}

/// `data[from..to]`, copied.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires from <= to <= data@.len(),
    ensures r@ == data@.subrange(from as int, to as int),
))]
fn copy(data: &[u8], from: usize, to: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(to - from);
    let mut i = from;
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            from <= i <= to <= data.len(),
            out@ == data@.subrange(from as int, i as int),
        decreases to - i
    ))]
    while i < to {
        out.push(data[i]);
        proof! { assert(data@.subrange(from as int, i + 1) =~= data@.subrange(from as int, i as int).push(data@[i as int])); }
        i += 1;
    }
    out
}

/// The parameter at `data[at..]` and where it ends.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires at <= data@.len(),
    ensures
        r matches Some((p, next)) ==> {
            &&& param_fits(p@)
            &&& next == at + enc_param(p@).len()
            &&& encoded_at(data@, at as int, enc_param(p@))
        },
        forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q))
            ==> (r matches Some((p, next)) && p@ == q && next == at + enc_param(q).len()),
))]
fn decode_param(data: &[u8], at: usize) -> Option<(Param, usize)> {
    if at >= data.len() {
        proof! {
            assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q)) implies false by {
                lemma_param_tag(data@, at as int, q);
            }
        }
        return None;
    }
    let tag = data[at];
    if tag == NULL {
        proof! {
            assert(data@.subrange(at as int, at + 1) =~= enc_param(ParamView::Null));
            assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q)) implies q == ParamView::Null by {
                lemma_param_tag(data@, at as int, q);
            }
        }
        return Some((Param::Null, at + 1));
    }
    if tag == INTEGER || tag == REAL {
        return decode_word(data, at);
    }
    if tag == TEXT || tag == BLOB {
        return decode_bytes(data, at);
    }
    proof! {
        assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q)) implies false by {
            lemma_param_tag(data@, at as int, q);
        }
    }
    None
}

/// An integer or real parameter at `data[at..]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires at < data@.len(), data@[at as int] == INTEGER || data@[at as int] == REAL,
    ensures
        r matches Some((p, next)) ==> {
            &&& param_fits(p@)
            &&& next == at + enc_param(p@).len()
            &&& encoded_at(data@, at as int, enc_param(p@))
        },
        forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q))
            ==> (r matches Some((p, next)) && p@ == q && next == at + enc_param(q).len()),
))]
fn decode_word(data: &[u8], at: usize) -> Option<(Param, usize)> {
    let tag = data[at];
    if data.len() - at - 1 < 8 {
        proof! {
            assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q)) implies false by {
                lemma_param_tag(data@, at as int, q);
            }
        }
        return None;
    }
    let w = read_u64(data, at + 1);
    let p = if tag == INTEGER { Param::Integer(w as i64) } else { Param::Real(w) };
    proof! {
        lemma_cast(0, w);
        assert(enc_param(p@) =~= seq![tag] + be8(w));
        assert(data@.subrange(at as int, at + 9) =~= seq![tag] + data@.subrange(at + 1, at + 9));
        assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q)) implies p@ == q && enc_param(q).len() == 9 by {
            lemma_param_tag(data@, at as int, q);
            let rest = enc_param(q).subrange(1, enc_param(q).len() as int);
            lemma_split(data@, at as int, seq![tag], rest);
            match q {
                ParamView::Integer(i) => {
                    assert(rest =~= be8(i as u64));
                    lemma_cast(i, w);
                }
                ParamView::Real(x) => {
                    assert(rest =~= be8(x));
                }
                _ => {}
            }
        }
    }
    Some((p, at + 9))
}

/// A text or blob parameter at `data[at..]`.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires at < data@.len(), data@[at as int] == TEXT || data@[at as int] == BLOB,
    ensures
        r matches Some((p, next)) ==> {
            &&& param_fits(p@)
            &&& next == at + enc_param(p@).len()
            &&& encoded_at(data@, at as int, enc_param(p@))
        },
        forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q))
            ==> (r matches Some((p, next)) && p@ == q && next == at + enc_param(q).len()),
))]
fn decode_bytes(data: &[u8], at: usize) -> Option<(Param, usize)> {
    let tag = data[at];
    if data.len() - at - 1 < 4 {
        proof! {
            assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q)) implies false by {
                lemma_param_tag(data@, at as int, q);
            }
        }
        return None;
    }
    let n = read_u32(data, at + 1) as usize;
    if data.len() - at - 5 < n {
        proof! {
            assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q)) implies false by {
                lemma_param_tag(data@, at as int, q);
                let rest = enc_param(q).subrange(1, enc_param(q).len() as int);
                lemma_split(data@, at as int, seq![tag], rest);
                match q {
                    ParamView::Text(b) | ParamView::Blob(b) => {
                        assert(rest =~= be4(b.len() as u32) + b);
                        lemma_split(data@, at + 1, be4(b.len() as u32), b);
                    }
                    _ => {}
                }
            }
        }
        return None;
    }
    let b = copy(data, at + 5, at + 5 + n);
    let p = if tag == TEXT { Param::Text(b) } else { Param::Blob(b) };
    proof! {
        assert(enc_param(p@) =~= seq![tag] + (be4(n as u32) + data@.subrange(at + 5, at + 5 + n)));
        assert(data@.subrange(at as int, at + 5 + n)
            =~= seq![tag] + (data@.subrange(at + 1, at + 5) + data@.subrange(at + 5, at + 5 + n)));
        assert forall|q: ParamView| #[trigger] param_fits(q) && encoded_at(data@, at as int, enc_param(q))
            implies p@ == q && enc_param(q).len() == 5 + n by {
            lemma_param_tag(data@, at as int, q);
            let rest = enc_param(q).subrange(1, enc_param(q).len() as int);
            lemma_split(data@, at as int, seq![tag], rest);
            match q {
                ParamView::Text(c) | ParamView::Blob(c) => {
                    assert(rest =~= be4(c.len() as u32) + c);
                    lemma_split(data@, at + 1, be4(c.len() as u32), c);
                    assert(c =~= data@.subrange(at + 5, at + 5 + n));
                }
                _ => {}
            }
        }
    }
    Some((p, at + 5 + n))
}

/// The statement at `data[at..]` and where it ends.
#[cfg_attr(feature = "verus", verus_verify)]
#[allow(clippy::too_many_lines, reason = "most of the lines are proof")]
#[cfg_attr(feature = "verus", verus_spec(r =>
    requires at <= data@.len(),
    ensures
        r matches Some((s, next)) ==> {
            &&& statement_fits(s@)
            &&& next == at + enc_statement(s@).len()
            &&& encoded_at(data@, at as int, enc_statement(s@))
        },
        forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q))
            ==> (r matches Some((s, next)) && s@ == q && next == at + enc_statement(q).len()),
))]
fn decode_statement(data: &[u8], at: usize) -> Option<(Statement, usize)> {
    if data.len() - at < 4 {
        proof! {
            assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q)) implies false by {
                lemma_statement_parts(data@, at as int, q);
            }
        }
        return None;
    }
    let n32 = read_u32(data, at);
    let n = n32 as usize;
    if data.len() - at - 4 < n {
        proof! {
            assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q)) implies false by {
                lemma_statement_parts(data@, at as int, q);
            }
        }
        return None;
    }
    let sql = copy(data, at + 4, at + 4 + n);
    proof! {
        assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q)) implies q.sql == sql@ by {
            lemma_statement_parts(data@, at as int, q);
            assert(q.sql.len() == n);
        }
    }
    if data.len() - at - 4 - n < 4 {
        proof! {
            assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q)) implies false by {
                lemma_statement_parts(data@, at as int, q);
            }
        }
        return None;
    }
    let count = read_u32(data, at + 4 + n);
    let start = at + 8 + n;
    let mut pos = start;
    let mut params: Vec<Param> = Vec::new();
    let mut i: u32 = 0;
    proof! {
        assert(data@.subrange(start as int, start as int) =~= enc_params(params_view(params@)));
        assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q))
            implies q.params.len() == count && params_view(params@) == q.params.take(0) by {
            lemma_statement_parts(data@, at as int, q);
            assert(params_view(params@) =~= q.params.take(0));
        }
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            at + 8 + n == start <= pos <= data.len(),
            sql@ == data@.subrange(at + 4, at + 4 + n),
            be4(n32) == data@.subrange(at as int, at + 4),
            n == n32,
            be4(count) == data@.subrange(at + 4 + n, start as int),
            params.len() == i,
            i <= count,
            data@.subrange(start as int, pos as int) == enc_params(params_view(params@)),
            forall|k: int| 0 <= k < params.len() ==> #[trigger] param_fits(params@[k]@),
            forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q)) ==> {
                &&& q.sql == sql@
                &&& q.params.len() == count
                &&& params_view(params@) == q.params.take(i as int)
                &&& pos == start + enc_params(q.params.take(i as int)).len()
            },
        decreases count - i
    ))]
    while i < count {
        let r = decode_param(data, pos);
        proof! {
            assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q))
                implies (r matches Some((p, next)) && p@ == q.params[i as int] && next == pos + enc_param(q.params[i as int]).len()) by {
                lemma_statement_parts(data@, at as int, q);
                lemma_param_in_list(data@, start as int, q.params, i as int);
                assert(param_fits(q.params[i as int]));
            }
        }
        match r {
            None => return None,
            Some((p, next)) => {
                proof! {
                    lemma_join(data@, start as int, enc_params(params_view(params@)), enc_param(p@));
                    assert(params_view(params@.push(p)) =~= params_view(params@).push(p@));
                    assert(params_view(params@).push(p@).drop_last() =~= params_view(params@));
                    assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q))
                        implies params_view(params@.push(p)) == q.params.take(i + 1)
                            && next == start + enc_params(q.params.take(i + 1)).len() by {
                        lemma_params_step(q.params, i as int);
                        assert(q.params.take(i + 1) =~= q.params.take(i as int).push(q.params[i as int]));
                    }
                }
                params.push(p);
                pos = next;
                i += 1;
            }
        }
    }
    let s = Statement { sql, params };
    proof! {
        assert(s@.params.len() == count);
        assert(data@.subrange(at as int, pos as int) =~= data@.subrange(at as int, at + 4) + data@.subrange(at + 4, at + 4 + n)
            + data@.subrange(at + 4 + n, start as int) + data@.subrange(start as int, pos as int));
        assert(data@.subrange(at as int, pos as int) =~= enc_statement(s@));
        assert forall|q: StatementView| #[trigger] statement_fits(q) && encoded_at(data@, at as int, enc_statement(q)) implies s@ == q by {
            assert(q.params.take(count as int) =~= q.params);
        }
    }
    Some((s, pos))
}

/// Decodes a batch. `None` if it is cut short, has an unknown tag, or has
/// bytes left over.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some(v) ==> batch_fits(statements_view(v@)) && enc_batch(statements_view(v@)) == data@,
        forall|q: Seq<StatementView>| #[trigger] batch_fits(q) && enc_batch(q) == data@
            ==> (r matches Some(v) && statements_view(v@) == q),
))]
#[must_use]
pub fn decode_batch(data: &[u8]) -> Option<Vec<Statement>> {
    let mut out: Vec<Statement> = Vec::new();
    let mut at: usize = 0;
    proof! {
        assert(data@.subrange(0, 0) =~= enc_batch(statements_view(out@)));
        assert forall|q: Seq<StatementView>| #[trigger] batch_fits(q) && enc_batch(q) == data@
            implies statements_view(out@) == q.take(0) by {
            assert(statements_view(out@) =~= q.take(0));
        }
    }
    #[cfg_attr(feature = "verus", verus_spec(
        invariant
            at <= data.len(),
            data@.subrange(0, at as int) == enc_batch(statements_view(out@)),
            batch_fits(statements_view(out@)),
            forall|q: Seq<StatementView>| #[trigger] batch_fits(q) && enc_batch(q) == data@ ==> {
                &&& out.len() <= q.len()
                &&& statements_view(out@) == q.take(out.len() as int)
                &&& at == enc_batch(q.take(out.len() as int)).len()
            },
        decreases data.len() - at
    ))]
    while at < data.len() {
        let r = decode_statement(data, at);
        proof! {
            assert forall|q: Seq<StatementView>| #[trigger] batch_fits(q) && enc_batch(q) == data@
                implies out.len() < q.len() && (r matches Some((s, next)) && s@ == q[out.len() as int]
                    && next == at + enc_statement(q[out.len() as int]).len()) by {
                if out.len() == q.len() {
                    assert(q.take(out.len() as int) =~= q);
                }
                lemma_statement_in_batch(data@, q, out.len() as int);
                assert(statement_fits(q[out.len() as int]));
            }
        }
        match r {
            None => return None,
            Some((s, next)) => {
                proof! {
                    let k = out.len() as int;
                    lemma_join(data@, 0, data@.subrange(0, at as int), enc_statement(s@));
                    assert(data@.subrange(0, at as int) =~= data@.subrange(0, at as int).subrange(0, at as int));
                    assert(data@.subrange(0, next as int) =~= data@.subrange(0, at as int) + data@.subrange(at as int, next as int));
                    assert(statements_view(out@.push(s)) =~= statements_view(out@).push(s@));
                    assert(statements_view(out@).push(s@).drop_last() =~= statements_view(out@));
                    assert forall|q: Seq<StatementView>| #[trigger] batch_fits(q) && enc_batch(q) == data@
                        implies statements_view(out@.push(s)) == q.take(k + 1)
                            && next == enc_batch(q.take(k + 1)).len() by {
                        assert(q.take(k + 1) =~= q.take(k).push(q[k]));
                        assert(q.take(k + 1).drop_last() =~= q.take(k));
                    }
                }
                out.push(s);
                at = next;
            }
        }
    }
    proof! {
        assert(data@.subrange(0, at as int) =~= data@);
        assert forall|q: Seq<StatementView>| #[trigger] batch_fits(q) && enc_batch(q) == data@
            implies statements_view(out@) == q by {
            lemma_batch_prefix(q, out.len() as int);
            assert(q.take(out.len() as int) =~= q);
        }
    }
    Some(out)
}

/// The frame at `data[at..]`: its sequence number and where its body starts
/// and ends. `None` if the header or the body runs past the end.
#[cfg_attr(feature = "verus", verus_verify)]
#[cfg_attr(feature = "verus", verus_spec(r =>
    ensures
        r matches Some((seq, start, end)) ==> {
            &&& start == at + 16
            &&& start <= end <= data@.len()
            &&& encoded_at(data@, at as int, enc_frame(seq, data@.subrange(start as int, end as int)))
        },
        forall|seq: u64, body: Seq<u8>| #[trigger] encoded_at(data@, at as int, enc_frame(seq, body))
            ==> r == Some((seq, (at + 16) as usize, (at + 16 + body.len()) as usize)),
))]
#[must_use]
pub fn frame_at(data: &[u8], at: usize) -> Option<(u64, usize, usize)> {
    if at > data.len() || data.len() - at < 16 {
        return None;
    }
    let seq = read_u64(data, at);
    let len = read_u64(data, at + 8);
    if len > (data.len() - at - 16) as u64 {
        proof! {
            assert forall|s: u64, body: Seq<u8>| #[trigger] encoded_at(data@, at as int, enc_frame(s, body)) implies false by {
                assert(enc_frame(s, body) =~= be8(s) + (be8(body.len() as u64) + body));
                lemma_split(data@, at as int, be8(s), be8(body.len() as u64) + body);
                lemma_split(data@, at + 8, be8(body.len() as u64), body);
            }
        }
        return None;
    }
    let end = at + 16 + len as usize;
    proof! {
        assert(enc_frame(seq, data@.subrange(at + 16, end as int))
            =~= data@.subrange(at as int, at + 8) + data@.subrange(at + 8, at + 16) + data@.subrange(at + 16, end as int));
        assert(data@.subrange(at as int, end as int)
            =~= data@.subrange(at as int, at + 8) + data@.subrange(at + 8, at + 16) + data@.subrange(at + 16, end as int));
        assert forall|s: u64, body: Seq<u8>| #[trigger] encoded_at(data@, at as int, enc_frame(s, body))
            implies s == seq && body.len() == len by {
            assert(enc_frame(s, body) =~= be8(s) + (be8(body.len() as u64) + body));
            lemma_split(data@, at as int, be8(s), be8(body.len() as u64) + body);
            lemma_split(data@, at + 8, be8(body.len() as u64), body);
        }
    }
    Some((seq, at + 16, end))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_is_fixed() {
        let mut out = Vec::new();
        let s = Statement { sql: b"x".to_vec(), params: vec![Param::Integer(-1), Param::Text(b"hi".to_vec())] };
        assert!(encode_statement(&mut out, &s));
        let expected: Vec<u8> = [
            &[0, 0, 0, 1, b'x', 0, 0, 0, 2][..],
            &[INTEGER, 255, 255, 255, 255, 255, 255, 255, 255],
            &[TEXT, 0, 0, 0, 2, b'h', b'i'],
        ]
        .concat();
        assert_eq!(out, expected);
        assert_eq!(decode_batch(&out), Some(vec![s]));
    }

    #[test]
    fn rejects_bad_batches() {
        let mut out = Vec::new();
        let s = Statement { sql: b"x".to_vec(), params: vec![Param::Null, Param::Real(1.5_f64.to_bits())] };
        assert!(encode_statement(&mut out, &s));
        for cut in 0..out.len() {
            assert!(cut == 0 || decode_batch(&out[..cut]).is_none());
        }
        assert_eq!(decode_batch(&[]), Some(vec![]));
        assert_eq!(decode_batch(&[0, 0, 0, 0, 0, 0, 0, 1, 9]), None);
    }

    #[test]
    fn frames_parse() {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&7_u64.to_be_bytes());
        bytes.extend_from_slice(&2_u64.to_be_bytes());
        bytes.extend_from_slice(b"ab");
        assert_eq!(frame_at(&bytes, 0), Some((7, 16, 18)));
        assert_eq!(frame_at(&bytes, 18), None);
        assert_eq!(frame_at(&bytes[..17], 0), None);
    }
}
