# LeanBuddy migration log

Implementation log for [AGENT_PROMPT.md](AGENT_PROMPT.md). Branch `leanbuddy-migration`. Newest entries at the
bottom of each section. Scratch and build material lives outside git in `~/leanbuddy-work/`.

## Phase 0 — workspace baseline (2026-10-09, Mac: Apple M4, 16 GB, macOS 15 / Darwin 24.6)

- `leanbuddy/` = copy of `prosabuddy-rocq/` (706 files; `BASELINE.md` dropped, `.gitignore` kept).
- `bun install` with Bun 1.3.10 (`replicate-prosa-buddy/.tools/bin/bun`, arm64): 1,678 packages.
- `bun run typecheck` (root, before any change): **4/4 packages pass** (5 s).
- `bun test --timeout 30000` in `packages/opencode` (before any change): **1,494 pass, 9 skip, 28 fail**, 1,531 tests
  in 103 files, 405 s. Log: `~/leanbuddy-work/baseline-test.log`.

Pre-existing failures (all 28 are environmental; none is a migration signal):

| Cause | Tests | Count |
|---|---|---|
| No Rocq toolchain on the Mac (`coqc`, `coqtop`, `fcc` absent) | `coq AST audit` ×3; `tool.task recursive proof agents` ×3; `tool.proof_plan bounded semantic review` ×3; `tool.proof-premise-audit` ×5; `proof edit transaction` ×3; `session.proof-workflow lemma scheduling > checkpoint scaffold compiles…` ×1; `tool.bash > allows read-only shell commands that mention the active transaction file` ×1 (exit 127) | 19 |
| Network (remote download / provider stream) | `Discovery.pull` ×4 (skill download from a URL); `session.llm.stream` ×4 (30 s timeouts) | 8 |
| Error classification of a socket reset | `session.message-v2.fromError > converts ECONNRESET socket errors to retryable APIError` | 1 |

(The PC baseline of the pristine tree was 129 pass / 9 fail on a subset with 5 s timeouts; the Mac run is the full
suite with 30 s timeouts.) The Rocq-dependent tests belong to modules that Phases 2–4 replace; their Lean
replacements must pass.

## Note status

`todo` / `done` / `deviated` (deviations are explained in the *Deviations* section).

| # | Note | Status | Phase | Commit / remark |
|---|---|---|---|---|
| 1 | [BACKEND_DECISION.md](migration-suggestions/BACKEND_DECISION.md) | todo | 1, 4 | |
| 2 | [gap-revisions/01-prompt.ts-revision.md](migration-suggestions/gap-revisions/01-prompt.ts-revision.md) | todo | 3–8 | |
| 3 | [gap-revisions/02-system-prompts/coqprover.txt-revision.md](migration-suggestions/gap-revisions/02-system-prompts/coqprover.txt-revision.md) | todo | 3–8 | |
| 4 | [gap-revisions/02-system-prompts/proof-workflow-principles.txt-revision.md](migration-suggestions/gap-revisions/02-system-prompts/proof-workflow-principles.txt-revision.md) | todo | 3–8 | |
| 5 | [gap-revisions/02-system-prompts/system.ts-revision.md](migration-suggestions/gap-revisions/02-system-prompts/system.ts-revision.md) | todo | 3–8 | |
| 6 | [gap-revisions/03-small-source-files/agent.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/agent.ts-revision.md) | todo | 3–8 | |
| 7 | [gap-revisions/03-small-source-files/compaction.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/compaction.ts-revision.md) | todo | 3–8 | |
| 8 | [gap-revisions/03-small-source-files/message-v2.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/message-v2.ts-revision.md) | todo | 3–8 | |
| 9 | [gap-revisions/03-small-source-files/run.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/run.ts-revision.md) | todo | 3–8 | |
| 10 | [gap-revisions/03-small-source-files/tui-dialog-status.tsx-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-dialog-status.tsx-revision.md) | todo | 3–8 | |
| 11 | [gap-revisions/03-small-source-files/tui-lsp.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-lsp.ts-revision.md) | todo | 3–8 | |
| 12 | [gap-revisions/03-small-source-files/tui-sidebar.tsx-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-sidebar.tsx-revision.md) | todo | 3–8 | |
| 13 | [gap-revisions/03-small-source-files/tui-sync.tsx-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-sync.tsx-revision.md) | todo | 3–8 | |
| 14 | [gap-revisions/04-audit-backend/checkpoint.ts-audit-revision.md](migration-suggestions/gap-revisions/04-audit-backend/checkpoint.ts-audit-revision.md) | todo | 3 | |
| 15 | [gap-revisions/04-audit-backend/coq-ast-audit.ts-revision.md](migration-suggestions/gap-revisions/04-audit-backend/coq-ast-audit.ts-revision.md) | todo | 3 | |
| 16 | [gap-revisions/04-audit-backend/coqc.ts-audit-revision.md](migration-suggestions/gap-revisions/04-audit-backend/coqc.ts-audit-revision.md) | todo | 3 | |
| 17 | [gap-revisions/04-audit-backend/removed-files.md](migration-suggestions/gap-revisions/04-audit-backend/removed-files.md) | todo | 3 | |
| 18 | [gap-revisions/04-audit-backend/task.ts-audit-revision.md](migration-suggestions/gap-revisions/04-audit-backend/task.ts-audit-revision.md) | todo | 3 | |
| 19 | [gap-revisions/04-audit-backend/validate_classified_ast.py-revision.md](migration-suggestions/gap-revisions/04-audit-backend/validate_classified_ast.py-revision.md) | todo | 3 | |
| 20 | [gap-revisions/05-benchmark-runner/opencode_our_local.sh-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/opencode_our_local.sh-revision.md) | todo | 8 | |
| 21 | [gap-revisions/05-benchmark-runner/opencode_our_prompt.md-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/opencode_our_prompt.md-revision.md) | todo | 8 | |
| 22 | [gap-revisions/05-benchmark-runner/opencode_runner_config-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/opencode_runner_config-revision.md) | todo | 8 | |
| 23 | [gap-revisions/05-benchmark-runner/run_casestudy_opencode_minprosa.py-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/run_casestudy_opencode_minprosa.py-revision.md) | todo | 8 | |
| 24 | [gap-revisions/05-benchmark-runner/run_casestudy_our_minprosa.py-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/run_casestudy_our_minprosa.py-revision.md) | todo | 8 | |
| 25 | [gap-revisions/07-tests/session__message-v2.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__message-v2.test.ts-revision.md) | todo | 3–5 | |
| 26 | [gap-revisions/07-tests/session__prompt.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__prompt.test.ts-revision.md) | todo | 3–5 | |
| 27 | [gap-revisions/07-tests/session__proof-edit-transaction.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-edit-transaction.test.ts-revision.md) | todo | 3–5 | |
| 28 | [gap-revisions/07-tests/session__proof-projection.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-projection.test.ts-revision.md) | todo | 3–5 | |
| 29 | [gap-revisions/07-tests/session__proof-route-ledger.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-route-ledger.test.ts-revision.md) | todo | 3–5 | |
| 30 | [gap-revisions/07-tests/session__proof-workflow.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-workflow.test.ts-revision.md) | todo | 3–5 | |
| 31 | [gap-revisions/07-tests/session__system.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__system.test.ts-revision.md) | todo | 3–5 | |
| 32 | [gap-revisions/07-tests/session__trace.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__trace.test.ts-revision.md) | todo | 3–5 | |
| 33 | [gap-revisions/07-tests/test_opencode_runner_config.py-revision.md](migration-suggestions/gap-revisions/07-tests/test_opencode_runner_config.py-revision.md) | todo | 3–5 | |
| 34 | [gap-revisions/07-tests/test_run_casestudy_continuation_prompt.py-revision.md](migration-suggestions/gap-revisions/07-tests/test_run_casestudy_continuation_prompt.py-revision.md) | todo | 3–5 | |
| 35 | [gap-revisions/07-tests/test_run_casestudy_decompose.py-revision.md](migration-suggestions/gap-revisions/07-tests/test_run_casestudy_decompose.py-revision.md) | todo | 3–5 | |
| 36 | [gap-revisions/07-tests/tool__apply_patch.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__apply_patch.test.ts-revision.md) | todo | 3–5 | |
| 37 | [gap-revisions/07-tests/tool__bash.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__bash.test.ts-revision.md) | todo | 3–5 | |
| 38 | [gap-revisions/07-tests/tool__coq-ast-audit.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-ast-audit.test.ts-revision.md) | todo | 3–5 | |
| 39 | [gap-revisions/07-tests/tool__coq-diagnostics.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-diagnostics.test.ts-revision.md) | todo | 3–5 | |
| 40 | [gap-revisions/07-tests/tool__coq-project.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-project.test.ts-revision.md) | todo | 3–5 | |
| 41 | [gap-revisions/07-tests/tool__coq-session.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-session.test.ts-revision.md) | todo | 3–5 | |
| 42 | [gap-revisions/07-tests/tool__coq-skill-hints.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-skill-hints.test.ts-revision.md) | todo | 3–5 | |
| 43 | [gap-revisions/07-tests/tool__edit.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__edit.test.ts-revision.md) | todo | 3–5 | |
| 44 | [gap-revisions/07-tests/tool__grep.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__grep.test.ts-revision.md) | todo | 3–5 | |
| 45 | [gap-revisions/07-tests/tool__proof-premise-audit.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__proof-premise-audit.test.ts-revision.md) | todo | 3–5 | |
| 46 | [gap-revisions/07-tests/tool__proof-review.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__proof-review.test.ts-revision.md) | todo | 3–5 | |
| 47 | [gap-revisions/07-tests/tool__proof-schema.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__proof-schema.test.ts-revision.md) | todo | 3–5 | |
| 48 | [gap-revisions/07-tests/tool__read.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__read.test.ts-revision.md) | todo | 3–5 | |
| 49 | [gap-revisions/07-tests/tool__task.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__task.test.ts-revision.md) | todo | 3–5 | |
| 50 | [gap-revisions/07-tests/tool__write.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__write.test.ts-revision.md) | todo | 3–5 | |
| 51 | [known-problem-fixes/lean_session-equivalence.md](migration-suggestions/known-problem-fixes/lean_session-equivalence.md) | todo | 4 | |
| 52 | [known-problem-fixes/lemma.txt-fixes.md](migration-suggestions/known-problem-fixes/lemma.txt-fixes.md) | todo | 5 | |
| 53 | [known-problem-fixes/prompt.ts-fixes.md](migration-suggestions/known-problem-fixes/prompt.ts-fixes.md) | todo | 5 | |
| 54 | [known-problem-fixes/proof-context.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-context.ts-fixes.md) | todo | 5 | |
| 55 | [known-problem-fixes/proof-plan.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-plan.ts-fixes.md) | todo | 5 | |
| 56 | [known-problem-fixes/proof-projection.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-projection.ts-fixes.md) | todo | 5 | |
| 57 | [known-problem-fixes/proof-schema.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-schema.ts-fixes.md) | todo | 5 | |
| 58 | [known-problem-fixes/proof-workflow.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-workflow.ts-fixes.md) | todo | 5 | |
| 59 | [known-problem-fixes/prover.txt-fixes.md](migration-suggestions/known-problem-fixes/prover.txt-fixes.md) | todo | 5 | |
| 60 | [known-problem-fixes/provider.ts-fixes.md](migration-suggestions/known-problem-fixes/provider.ts-fixes.md) | todo | 5 | |
| 61 | [known-problem-fixes/whole-lemma.txt-fixes.md](migration-suggestions/known-problem-fixes/whole-lemma.txt-fixes.md) | todo | 5 | |
| 62 | [prompt-advices/prompt_revision.md](migration-suggestions/prompt-advices/prompt_revision.md) | todo | 5 | |
| 63 | [skill-advices/count-bridging/SKILL.md](migration-suggestions/skill-advices/count-bridging/SKILL.md) | todo | 5 | |
| 64 | [skill-advices/failure-signature/SKILL.md](migration-suggestions/skill-advices/failure-signature/SKILL.md) | todo | 5 | |
| 65 | [skill-advices/goal/SKILL.md](migration-suggestions/skill-advices/goal/SKILL.md) | todo | 5 | |
| 66 | [skill-advices/guide/SKILL.md](migration-suggestions/skill-advices/guide/SKILL.md) | todo | 5 | |
| 67 | [skill-advices/math/SKILL.md](migration-suggestions/skill-advices/math/SKILL.md) | todo | 5 | |
| 68 | [skill-advices/parameter/SKILL.md](migration-suggestions/skill-advices/parameter/SKILL.md) | todo | 5 | |
| 69 | [skill-advices/prosabuddy-guard-recovery/SKILL.md](migration-suggestions/skill-advices/prosabuddy-guard-recovery/SKILL.md) | todo | 5 | |
| 70 | [skill-advices/tactics/SKILL.md](migration-suggestions/skill-advices/tactics/SKILL.md) | todo | 5 | |
| 71 | [tools-advices/01-core-tools/checkpoint-revision.md](migration-suggestions/tools-advices/01-core-tools/checkpoint-revision.md) | todo | 2/5 | |
| 72 | [tools-advices/01-core-tools/coq-session-revision.md](migration-suggestions/tools-advices/01-core-tools/coq-session-revision.md) | todo | 2/5 | |
| 73 | [tools-advices/01-core-tools/coqc-revision.md](migration-suggestions/tools-advices/01-core-tools/coqc-revision.md) | todo | 2/5 | |
| 74 | [tools-advices/01-core-tools/coqtop-revision.md](migration-suggestions/tools-advices/01-core-tools/coqtop-revision.md) | todo | 2/5 | |
| 75 | [tools-advices/01-core-tools/petanque-revision.md](migration-suggestions/tools-advices/01-core-tools/petanque-revision.md) | todo | 2/5 | |
| 76 | [tools-advices/01-core-tools/proof-plan-revision.md](migration-suggestions/tools-advices/01-core-tools/proof-plan-revision.md) | todo | 2/5 | |
| 77 | [tools-advices/02-adapted-tools/apply_patch-revision.md](migration-suggestions/tools-advices/02-adapted-tools/apply_patch-revision.md) | todo | 2/5 | |
| 78 | [tools-advices/02-adapted-tools/bash-revision.md](migration-suggestions/tools-advices/02-adapted-tools/bash-revision.md) | todo | 2/5 | |
| 79 | [tools-advices/02-adapted-tools/edit-revision.md](migration-suggestions/tools-advices/02-adapted-tools/edit-revision.md) | todo | 2/5 | |
| 80 | [tools-advices/02-adapted-tools/lsp-revision.md](migration-suggestions/tools-advices/02-adapted-tools/lsp-revision.md) | todo | 2/5 | |
| 81 | [tools-advices/02-adapted-tools/multiedit-revision.md](migration-suggestions/tools-advices/02-adapted-tools/multiedit-revision.md) | todo | 2/5 | |
| 82 | [tools-advices/02-adapted-tools/read-revision.md](migration-suggestions/tools-advices/02-adapted-tools/read-revision.md) | todo | 2/5 | |
| 83 | [tools-advices/02-adapted-tools/task-revision.md](migration-suggestions/tools-advices/02-adapted-tools/task-revision.md) | todo | 2/5 | |
| 84 | [tools-advices/02-adapted-tools/write-revision.md](migration-suggestions/tools-advices/02-adapted-tools/write-revision.md) | todo | 2/5 | |
| 85 | [tools-advices/03-custom-tools/coq-check-revision.md](migration-suggestions/tools-advices/03-custom-tools/coq-check-revision.md) | todo | 2/5 | |
| 86 | [tools-advices/04-helper-modules/coq-ast-audit-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-ast-audit-revision.md) | todo | 2/5 | |
| 87 | [tools-advices/04-helper-modules/coq-diagnostics-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-diagnostics-revision.md) | todo | 2/5 | |
| 88 | [tools-advices/04-helper-modules/coq-project-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-project-revision.md) | todo | 2/5 | |
| 89 | [tools-advices/04-helper-modules/coq-skill-hints-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-skill-hints-revision.md) | todo | 2/5 | |
| 90 | [tools-advices/04-helper-modules/coq-style-guard-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-style-guard-revision.md) | todo | 2/5 | |
| 91 | [tools-advices/04-helper-modules/edit-conflict-guard-revision.md](migration-suggestions/tools-advices/04-helper-modules/edit-conflict-guard-revision.md) | todo | 2/5 | |
| 92 | [tools-advices/04-helper-modules/proof-plan-identifiers-revision.md](migration-suggestions/tools-advices/04-helper-modules/proof-plan-identifiers-revision.md) | todo | 2/5 | |
| 93 | [tools-advices/04-helper-modules/proof-premise-audit-revision.md](migration-suggestions/tools-advices/04-helper-modules/proof-premise-audit-revision.md) | todo | 2/5 | |
| 94 | [tools-advices/04-helper-modules/proof-schema-revision.md](migration-suggestions/tools-advices/04-helper-modules/proof-schema-revision.md) | todo | 2/5 | |
| 95 | [tools-advices/04-helper-modules/registry-revision.md](migration-suggestions/tools-advices/04-helper-modules/registry-revision.md) | todo | 2/5 | |
| 96 | [tools-advices/04-helper-modules/tool-revision.md](migration-suggestions/tools-advices/04-helper-modules/tool-revision.md) | todo | 2/5 | |
| 97 | [tools-advices/05-session-workflow/lemma-assignment-revision.md](migration-suggestions/tools-advices/05-session-workflow/lemma-assignment-revision.md) | todo | 2/5 | |
| 98 | [tools-advices/05-session-workflow/proof-context-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-context-revision.md) | todo | 2/5 | |
| 99 | [tools-advices/05-session-workflow/proof-edit-transaction-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-edit-transaction-revision.md) | todo | 2/5 | |
| 100 | [tools-advices/05-session-workflow/proof-policy-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-policy-revision.md) | todo | 2/5 | |
| 101 | [tools-advices/05-session-workflow/proof-projection-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-projection-revision.md) | todo | 2/5 | |
| 102 | [tools-advices/05-session-workflow/proof-route-ledger-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-route-ledger-revision.md) | todo | 2/5 | |
| 103 | [tools-advices/05-session-workflow/proof-workflow-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-workflow-revision.md) | todo | 2/5 | |
| 104 | [tools-advices/05-session-workflow/session-proof-revision.md](migration-suggestions/tools-advices/05-session-workflow/session-proof-revision.md) | todo | 2/5 | |
| 105 | [tools-advices/06-session-storage/proof-edit-transaction.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/proof-edit-transaction.sql-revision.md) | todo | 2/5 | |
| 106 | [tools-advices/06-session-storage/proof-route-ledger.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/proof-route-ledger.sql-revision.md) | todo | 2/5 | |
| 107 | [tools-advices/06-session-storage/session-proof-workflow.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/session-proof-workflow.sql-revision.md) | todo | 2/5 | |
| 108 | [tools-advices/06-session-storage/session-proof.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/session-proof.sql-revision.md) | todo | 2/5 | |
| 109 | [tools-advices/07-lsp/client-revision.md](migration-suggestions/tools-advices/07-lsp/client-revision.md) | todo | 2/5 | |
| 110 | [tools-advices/07-lsp/index-revision.md](migration-suggestions/tools-advices/07-lsp/index-revision.md) | todo | 2/5 | |
| 111 | [tools-advices/07-lsp/language-revision.md](migration-suggestions/tools-advices/07-lsp/language-revision.md) | todo | 2/5 | |
| 112 | [tools-advices/07-lsp/server-revision.md](migration-suggestions/tools-advices/07-lsp/server-revision.md) | todo | 2/5 | |

## Deviations and note corrections

(none yet)

## Phase log

