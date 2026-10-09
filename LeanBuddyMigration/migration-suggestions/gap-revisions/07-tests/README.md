# §7 Tests — revision set

Rule (DECISIONS R6): port the tests of translated modules to Lean fixtures; drop tests whose subject was removed or
replaced; tests that need a live Lean/Pantograph/`lake` run become **integration tests** gated by
`PROSABUDDY_LEAN_INTEGRATION=1` (the unit suite must run without a Lean installation). Shared Lean fixtures:
a minimal Lake project under `test/fixture/lean-project/` (pinned to the package toolchain, v4.33.1) containing one
`Statement.lean` / `Solution.lean` pair with two `:= (by …)` regions.

| Test file | Tests | Rocq lines | Live | Decision | Revision |
|---|---|---|---|---|---|
| `session/message-v2.test.ts` | 25 | 7 | 0 | Port | [session__message-v2.test.ts-revision.md](session__message-v2.test.ts-revision.md) |
| `session/prompt.test.ts` | 18 | 44 | 6 | Port | [session__prompt.test.ts-revision.md](session__prompt.test.ts-revision.md) |
| `session/proof-edit-transaction.test.ts` | 25 | 77 | 5 | Port | [session__proof-edit-transaction.test.ts-revision.md](session__proof-edit-transaction.test.ts-revision.md) |
| `session/proof-projection.test.ts` | 4 | 9 | 0 | Port | [session__proof-projection.test.ts-revision.md](session__proof-projection.test.ts-revision.md) |
| `session/proof-route-ledger.test.ts` | 10 | 11 | 0 | Port | [session__proof-route-ledger.test.ts-revision.md](session__proof-route-ledger.test.ts-revision.md) |
| `session/proof-workflow.test.ts` | 107 | 458 | 28 | Port in stages | [session__proof-workflow.test.ts-revision.md](session__proof-workflow.test.ts-revision.md) |
| `session/system.test.ts` | 1 | 1 | 0 | Port | [session__system.test.ts-revision.md](session__system.test.ts-revision.md) |
| `session/trace.test.ts` | 1 | 2 | 2 | Port | [session__trace.test.ts-revision.md](session__trace.test.ts-revision.md) |
| `tool/apply_patch.test.ts` | 27 | 3 | 0 | Port | [tool__apply_patch.test.ts-revision.md](tool__apply_patch.test.ts-revision.md) |
| `tool/bash.test.ts` | 22 | 23 | 5 | Port | [tool__bash.test.ts-revision.md](tool__bash.test.ts-revision.md) |
| `tool/coq-ast-audit.test.ts` | 5 | 22 | 0 | Drop and replace | [tool__coq-ast-audit.test.ts-revision.md](tool__coq-ast-audit.test.ts-revision.md) |
| `tool/coq-diagnostics.test.ts` | 3 | 10 | 0 | Port (rename) | [tool__coq-diagnostics.test.ts-revision.md](tool__coq-diagnostics.test.ts-revision.md) |
| `tool/coq-project.test.ts` | 11 | 9 | 0 | Port (rename) | [tool__coq-project.test.ts-revision.md](tool__coq-project.test.ts-revision.md) |
| `tool/coq-session.test.ts` | 11 | 67 | 1 | Rewrite | [tool__coq-session.test.ts-revision.md](tool__coq-session.test.ts-revision.md) |
| `tool/coq-skill-hints.test.ts` | 6 | 3 | 0 | Port | [tool__coq-skill-hints.test.ts-revision.md](tool__coq-skill-hints.test.ts-revision.md) |
| `tool/edit.test.ts` | 30 | 8 | 0 | Port | [tool__edit.test.ts-revision.md](tool__edit.test.ts-revision.md) |
| `tool/grep.test.ts` | 7 | 4 | 0 | Port | [tool__grep.test.ts-revision.md](tool__grep.test.ts-revision.md) |
| `tool/proof-premise-audit.test.ts` | 5 | 10 | 0 | Port | [tool__proof-premise-audit.test.ts-revision.md](tool__proof-premise-audit.test.ts-revision.md) |
| `tool/proof-review.test.ts` | 39 | 98 | 0 | Port | [tool__proof-review.test.ts-revision.md](tool__proof-review.test.ts-revision.md) |
| `tool/proof-schema.test.ts` | 12 | 17 | 0 | Port | [tool__proof-schema.test.ts-revision.md](tool__proof-schema.test.ts-revision.md) |
| `tool/read.test.ts` | 22 | 4 | 0 | Port | [tool__read.test.ts-revision.md](tool__read.test.ts-revision.md) |
| `tool/task.test.ts` | 13 | 51 | 6 | Port | [tool__task.test.ts-revision.md](tool__task.test.ts-revision.md) |
| `tool/write.test.ts` | 16 | 8 | 0 | Port | [tool__write.test.ts-revision.md](tool__write.test.ts-revision.md) |

Runner tests (Python, `scripts/scripts_junyi/`):

| Test file | Decision | Revision |
|---|---|---|
| `test_opencode_runner_config.py` | Port | [test_opencode_runner_config.py-revision.md](test_opencode_runner_config.py-revision.md) |
| `test_run_casestudy_continuation_prompt.py` | Port | [test_run_casestudy_continuation_prompt.py-revision.md](test_run_casestudy_continuation_prompt.py-revision.md) |
| `test_run_casestudy_decompose.py` | Drop | [test_run_casestudy_decompose.py-revision.md](test_run_casestudy_decompose.py-revision.md) |
