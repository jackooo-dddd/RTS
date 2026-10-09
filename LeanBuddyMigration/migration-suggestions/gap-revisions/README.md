# Gap revisions

Concrete per-file changes for every item that GAPS.md listed as open. Decisions they follow: [../DECISIONS.md](../DECISIONS.md).
Code links point at the pure upstream baseline `LeanBuddyMigration/prosabuddy-rocq` (ProsaBuddy 8e1de8c).

| GAPS item | Files | Revision |
|---|---|---|
| §1 runtime controller | `session/prompt.ts` | [01-prompt.ts-revision.md](01-prompt.ts-revision.md) |
| §2 system prompts | `coqprover.txt` (→ `leanprover.txt`), `proof-workflow-principles.txt`, `system.ts` | [02-system-prompts/](02-system-prompts) |
| §3 smaller source files | `agent.ts`, `compaction.ts`, `cli/cmd/run.ts`, `message-v2.ts`, 4 TUI files | [03-small-source-files/](03-small-source-files) |
| §4 audit backend | `coq-ast-audit.ts` (→ `lean-gate.ts`), `validate_classified_ast.py`, audit calls in `coqc.ts`/`checkpoint.ts`/`task.ts`, 9 deleted files | [04-audit-backend/](04-audit-backend/README.md) |
| §5 benchmark runner | 5 used runner files; 20+ unused scripts dropped | [05-benchmark-runner/](05-benchmark-runner/README.md) |
| §6 interactive backend | decided earlier | [../BACKEND_DECISION.md](../BACKEND_DECISION.md) |
| §7 tests | 23 TypeScript test files, 3 Python runner tests | [07-tests/](07-tests/README.md) |
| §8 unused framework files | removed | [../GAPS.md](../GAPS.md) §8 |

Order to implement (dependencies first): D2 tool names → §4 gate → §6 `lean_session` (Pantograph) → §1, §2, §3 → §7 tests
for those modules (port each test together with its module) → **§5 runner last**, once the app translation is complete
(only its four interface points, listed in the §5 README, are fixed now).
