#!/usr/bin/env python3
"""Lists every function in the workspace and whether Verus checks it, and
writes docs/coverage.md.

Verus (in attribute mode) checks a function exactly when the function, or
the `impl`/`trait` around it, carries `verus_verify`, or it sits in a
`verus! { }` block. Such a function is listed as `spec` when it states a
`requires`/`ensures` (or implements a trait method that does), and as
`checked` when Verus proves only that it cannot panic or overflow. Spec and
proof functions are ghost code and are not listed.

Every other function must have an entry in scripts/unverified.txt saying why
it is outside the proofs; `--check` fails on one without an entry, on an
entry that no longer matches a function, on `external_body`, and on a stale
docs/coverage.md.

    python3 scripts/coverage.py          # rewrite docs/coverage.md
    python3 scripts/coverage.py --check  # what CI runs
"""

import re
import sys
from collections import Counter
from pathlib import Path

CRATES = ["crates/msapi-core/src", "crates/msapi-server/src"]
ALLOW = Path("scripts/unverified.txt")
OUT = Path("docs/coverage.md")


def lex(src):
    """Yields (char, line) for code outside comments, strings and char
    literals, with each string or char literal replaced by a single `"`."""
    i, line, n = 0, 1, len(src)
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            yield c, line
            i += 1
        elif src.startswith("//", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif src.startswith("/*", i):
            j = src.find("*/", i + 2)
            line += src.count("\n", i, j)
            i = j + 2
        elif c == "r" and re.match(r'r#*"', src[i:]) and not (i and (src[i - 1].isalnum() or src[i - 1] == "_")):
            hashes = re.match(r"r(#*)\"", src[i:]).group(1)
            end = src.find('"' + hashes, i + 2 + len(hashes))
            line += src.count("\n", i, end)
            yield '"', line
            i = end + 1 + len(hashes)
        elif c == '"' or (c == "b" and src.startswith('b"', i) and not (i and (src[i - 1].isalnum() or src[i - 1] == "_"))):
            j = i + (2 if c == "b" else 1)
            while src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            line += src.count("\n", i, j)
            yield '"', line
            i = j + 1
        elif c == "'" and re.match(r"'(\\.[^']*|[^'\\])'", src[i:]):
            m = re.match(r"'(\\.[^']*|[^'\\])'", src[i:])
            yield '"', line
            i += len(m.group(0))
        else:
            yield c, line
            i += 1


FN = re.compile(r"\bfn\s+(\w+)")
GHOST = re.compile(r"\b(spec|proof)\s+fn\b|\bspec\s*\(\s*checked\s*\)\s*fn\b")


def items(path):
    """(name, line, status, header) for each function with a body that is
    not nested in another function, in a test module or ghost."""
    src = path.read_text()
    out = []
    # Each frame: (kind, header, verified, skip)
    stack = [("file", "", False, False)]
    header, start = [], None
    attr = 0  # bracket depth inside a `#[...]` attribute
    prev = ""
    for c, line in lex(src):
        if attr:
            attr += {"[": 1, "]": -1}.get(c, 0)
            header.append(c)
            continue
        if c == "[" and prev.rstrip().endswith(("#", "#!")):
            attr = 1
            header.append(c)
            prev += c
            continue
        prev = (prev + c)[-2:] if not c.isspace() else prev
        if c in "{;}":
            text = "".join(header)
            if c == "{":
                kind, verified, skip = classify(text, stack)
                if kind == "fn" and not skip:
                    name = FN.search(text).group(1)
                    out.append((name, start or line, status(text, stack, verified), owner(stack)))
                stack.append((kind, text, verified, skip))
            elif c == "}" and len(stack) > 1:
                stack.pop()
            header, start = [], None
        else:
            if start is None and not c.isspace():
                start = line
            header.append(c)
    return out


def classify(text, stack):
    parent_kind, _, parent_verified, parent_skip = stack[-1]
    t = text.strip()
    skip = parent_skip or parent_kind in ("fn", "other")
    if re.search(r"#\[cfg\(test\)\]", t):
        skip = True
    in_verus = any(k == "verus" for k, *_ in stack)
    if re.search(r"\bverus!\s*$", t):
        return "verus", True, skip
    if FN.search(t) and not re.search(r"=\s*\|", t):
        ghost = bool(GHOST.search(t)) or "external_body" in t and False
        verified = "verus_verify" in t or parent_verified or in_verus
        return "fn", verified, skip or ghost
    if re.search(r"\bimpl\b", t) and not re.search(r"\bfn\b", t):
        return "impl", "verus_verify" in t or in_verus, skip
    if re.search(r"\btrait\s+\w+", t):
        return "trait", "verus_verify" in t or in_verus, skip
    if re.search(r"\bmod\s+\w+\s*$", t):
        return "mod", False, skip
    if re.search(r"\bmacro_rules!\s*\w+\s*$", t):
        return "macro", False, skip
    if parent_kind == "macro" or (parent_kind == "other" and any(k == "macro" for k, *_ in stack) and not any(k == "fn" for k, *_ in stack)):
        # Inside a macro_rules arm: the expansion's items.
        return "macro", False, skip
    return "other", False, skip


def status(text, stack, verified):
    if "external_body" in text:
        return "external_body"
    if not verified:
        return "unverified"
    if re.search(r"\b(ensures|requires)\b", text):
        return "spec"
    _, impl, _, _ = stack[-1]
    if re.search(r"\bimpl\b.*\bfor\b", impl):
        return "spec"  # the trait's spec (vstd's or ours) is what Verus checks it against
    return "checked"


def owner(stack):
    for kind, text, *_ in reversed(stack):
        if kind in ("impl", "trait"):
            t = re.sub(r"#\[[^\]]*(\[[^\]]*\][^\]]*)*\]", "", text)
            t = re.sub(r"\s+", " ", t).strip()
            t = re.sub(r"^(unsafe )?impl(<.*?>)? ", "", t) if t.startswith("impl") else re.sub(r"^.*?trait ", "trait ", t)
            return strip_generics(t.split(" where ")[0]).strip()
    return ""


def strip_generics(t):
    """`TryFrom<String> for Level<T>` → `TryFrom for Level`."""
    out, depth = [], 0
    for c in t:
        if c == "<":
            depth += 1
        elif c == ">" and depth:
            depth -= 1
        elif not depth:
            out.append(c)
    return "".join(out)


def scan():
    rows = []
    for crate in CRATES:
        for path in sorted(Path(crate).rglob("*.rs")):
            for name, line, st, own in items(path):
                rows.append((str(path), line, f"{own}::{name}" if own else name, st))
    return rows


def allowlist():
    entries = {}
    for raw in ALLOW.read_text().splitlines():
        if not raw.strip() or raw.startswith("#"):
            continue
        key, category, reason = (p.strip() for p in raw.split("|", 2))
        entries.setdefault(key, []).append((category, reason))
    return entries


def render(rows, allow):
    by = Counter((Path(p).parts[1], st) for p, _, _, st in rows)
    lines = [
        "# Verification coverage",
        "",
        "Generated by `scripts/coverage.py`; CI fails when it is stale. Every",
        "function with a body in `msapi-core` and `msapi-server` is listed by",
        "whether Verus checks it:",
        "",
        "- **spec**: Verus proves it meets a stated `requires`/`ensures` (its own, or",
        "  the trait method's it implements), and that it cannot panic or overflow.",
        "- **checked**: Verus proves only that it cannot panic or overflow.",
        "- **unverified**: outside the proofs, for the reason in",
        "  `scripts/unverified.txt` (shown below).",
        "",
        "| crate | spec | checked | unverified |",
        "|---|---:|---:|---:|",
    ]
    for crate in ("msapi-core", "msapi-server"):
        lines.append(f"| `{crate}` | {by[(crate, 'spec')]} | {by[(crate, 'checked')]} | {by[(crate, 'unverified')]} |")
    cats = Counter()
    seen = Counter()
    for p, _, name, st in rows:
        if st == "unverified":
            cats[allow_entry(p, name, allow, seen)[0]] += 1
    lines += ["", "## Unverified functions by reason", "", "| reason | functions |", "|---|---:|"]
    for cat, n in sorted(cats.items()):
        lines.append(f"| {CATEGORY.get(cat, cat)} | {n} |")
    lines += ["", "## Every function", "", "| function | file | status | why unverified |", "|---|---|---|---|"]
    seen = Counter()
    for p, line, name, st in rows:
        why = ""
        if st == "unverified":
            why = allow_entry(p, name, allow, seen)[1]
        lines.append(f"| `{name}` | `{p}:{line}` | {st} | {why} |")
    return "\n".join(lines) + "\n"


CATEGORY = {
    "io": "I/O: SQL, HTTP, clock, randomness, process",
    "lib": "hands data to or from an outside library (serde, rusqlite, ring, tiny_http)",
    "shim": "trait shim forwarding to a proven function (`Display`, `FromStr`, serde)",
    "glue": "moves data between a proven function and the server's types",
    "test": "test or example support",
}


def allow_entry(p, name, allow, seen):
    """The (category, reason) for this function. Same-named functions in one
    file (two `From` impls, say) take their entries in file order."""
    key = f"{p}::{name}"
    e = allow.get(key)
    if not e:
        return ("missing", "")
    i = min(seen[key], len(e) - 1)
    seen[key] += 1
    return e[i]


def main():
    rows = scan()
    allow = allowlist()
    problems = []
    unverified = Counter(f"{p}::{n}" for p, _, n, st in rows if st == "unverified")
    for p, line, name, st in rows:
        key = f"{p}::{name}"
        if st == "external_body":
            problems.append(f"{p}:{line}: {name} is external_body")
        elif st == "unverified" and key not in allow:
            problems.append(f"{p}:{line}: {name} is unverified and has no entry in {ALLOW}")
    for key, entries in allow.items():
        if unverified[key] == 0:
            problems.append(f"{ALLOW}: {key} matches no unverified function (remove it)")
        for cat, _ in entries:
            if cat not in CATEGORY:
                problems.append(f"{ALLOW}: {key} has unknown category {cat}")
    text = render(rows, allow)
    if "--check" in sys.argv:
        if OUT.read_text() != text:
            problems.append(f"{OUT} is stale; run python3 scripts/coverage.py")
    else:
        OUT.write_text(text)
    for p in problems:
        print(p)
    sys.exit(1 if problems else 0)


main()
