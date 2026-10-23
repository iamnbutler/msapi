# AGENTS

msapi is a hand-rolled MapleStory API: a central service that MapleStory tools
read from and write to. See `README.md` for the API and `docs/` for design notes.

## Working in this repo: lane

Every change happens in a lane, never in the main checkout and never with a
bare `git worktree add`.

1. `lane new <name>`, then work in the printed tree (`.lane/trees/<name>`).
2. `lane why <path>` before editing a file, to read its notes.
3. Commit. Add `Why: <path> | <note>` trailers only for non-obvious constraints.
4. `lane check`, then confirm, replace or retire any stale notes it lists.
5. `lane push`, open a PR with `gh pr create`, and squash-merge it.
6. In the main checkout: `git pull --ff-only`, then `lane prune --dry-run`, and
   `lane rm <name>` for merged lanes that prune misses.

<!-- lane:protocol -->
## Context memory

- Before editing a file, read `.lane/memory/<path>/` if it exists, or run `lane why <path>`.
- Record non-obvious findings with `lane note add <path> -a <anchor> "..."`.
- Do not edit `.lane/` by hand; landing manages it.
- Land with `lane merge`, or `lane push` where trunk is protected, then `lane prune` once it merges.
- Detailed workflow lives in `.agents/skills/lane/SKILL.md`; run `lane install skill` if it is absent.
<!-- /lane:protocol -->
