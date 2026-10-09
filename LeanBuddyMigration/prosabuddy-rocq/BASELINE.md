# ProsaBuddy, Rocq version: pure upstream commit 8e1de8c (source to translate)

Unmodified ProsaBuddy source at upstream commit `8e1de8c` ("Fix proof contracts, lookup recovery, and Coq goal
validation", 2026-10-09), github.com/liujunyixmu/prosabuddy. No replicate-prosa-buddy patches.

Built 2026-10-09 after the local upstream checkout was deleted:
- everything from `prosabuddy/` at this repository's commit `d577db4b` (= upstream `f692cb7` + the "Prosabuddy trys"
  scripts commit `4310344`), except `prosaworkspace/` (the bundled Coq Prosa sources, ~2,400 files; the same
  Prosa v0.6 + classic sources are in `replicate-prosa-buddy/prosa_v06/`);
- overlaid with the three files upstream `8e1de8c` changed (`packages/opencode/src/session/prompt.ts`,
  `session/proof-workflow.ts`, `tool/coq-session.ts`) and their three test files, taken from the 8e1de8c checkout
  before it was deleted. `src/` was checked file-by-file against that checkout.

Removed afterwards (2026-10-09, user decision: unused in the replication and not translated): `.opencode/agent/`
(8 agent definitions: casestudy-prover, coq-prover, docs, duplicate-pr, paper-analyst, proof-orchestrator,
translator, triage), `.opencode/command/` (9 slash commands), the custom tools `coq-proof-dag`, `coq-serapi`,
`pdf-read`, `github-pr-search`, `github-triage` (`.opencode/tool/`), and `.opencode/glossary/`, `.opencode/themes/`. They remain in git at this repository's commit
`d577db4b` under `prosabuddy/.opencode/`.

Location: `LeanBuddyMigration/prosabuddy-rocq/` (moved here from `replicate-prosa-buddy/prosabuddy-upstream-8e1de8c/`
on 2026-10-09). Use: the source the Lean port is translated from; every code link in
`../migration-suggestions/` points here. Do not run or patch this tree. The runnable Rocq trees used by the
replication stay in `replicate-prosa-buddy/`: `prosabuddy/` (patched f692cb7) and `prosabuddy-8e1de8c/`
(8e1de8c + replicate patches); `node_modules` is not included here.
