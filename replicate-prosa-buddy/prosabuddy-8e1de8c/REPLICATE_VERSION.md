# prosabuddy-8e1de8c (replicate-prosa-buddy)

ProsaBuddy upstream commit `8e1de8c` ("Fix proof contracts, lookup recovery, and Coq goal validation", 2026-10-09)
with the replicate-prosa-buddy patches carried over. Built 2026-10-09 from `../prosabuddy` (patched `f692cb7`).

- `session/prompt.ts`, `session/proof-workflow.ts`, `tool/coq-session.ts`: three-way merge
  (`git merge-file` ours = patched f692cb7, base = f692cb7, theirs = 8e1de8c).
- Dropped as superseded by upstream's new contract parser (`parseAttributes`, `attrList`): patch 3 (JSON-style
  `depends_on` lists) and patch 4 (`parseMarkerAttributes`). Upstream's versions are used verbatim.
- Kept unchanged: patches 1, 2, 5, 6, 8, 11/11b/15 (strict statement review), 12, 13, 14, 16 (fcc loadpath) and
  the files only we changed (normal-form.ts, compile-verdict.ts, checkpoint.ts, coqc.ts, task.ts,
  proof-context.ts, proof-projection.ts, coq-ast-audit.ts).
- `packages/opencode/test/` is upstream 8e1de8c (for checking the merge only).
