# Lean 4 Migration Recommendations for ProsaBuddy Tools

> **Read first:** [`../KNOWN_PROBLEMS.md`](../KNOWN_PROBLEMS.md) (structural problems found in the replication runs that must be decided before porting) and [`../GAPS.md`](../GAPS.md) (Rocq-specific parts not yet covered by these notes).
> **Code baseline:** all code links point at the pure upstream ProsaBuddy commit `8e1de8c` in [`LeanBuddyMigration/prosabuddy-rocq`](../../prosabuddy-rocq/BASELINE.md) (no replication patches). Notes added for 8e1de8c: `coq-session-revision.md` §6 (kernel entry-goal check) and `proof-workflow-revision.md` §8–9 (contract parser, lookup guard).

These 42 per-file notes are organized into seven categories. Each item identifies code locations, current behavior, migration recommendations, and change size; recommendations for six `.txt` files appear in their corresponding tool notes. Lean backend approaches described here are proposals, not implemented functionality.

**Structural Changes to Settle First**

1. Define Lean proof-block range representation first, and use it consistently in the [workflow](05-session-workflow/proof-workflow-revision.md), [edit transactions](05-session-workflow/proof-edit-transaction-revision.md), and editing tools.
2. Define the responsibilities of the [project environment](04-helper-modules/coq-project-revision.md), [LSP diagnostics and lookups](07-lsp/index-revision.md), and [interactive sessions](01-core-tools/coq-session-revision.md). Goal queries and tactic-state execution/restoration require separate adaptation. **Decided:** Pantograph for interactive sessions (tactics, goals, backtracking), Lean LSP for file-level diagnostics, `lake build` for final verification — see [`../BACKEND_DECISION.md`](../BACKEND_DECISION.md).
3. Define [declaration and proof audits](04-helper-modules/coq-ast-audit-revision.md), local certificates, and final completion criteria before connecting [checkpoint](01-core-tools/checkpoint-revision.md) and [task](02-adapted-tools/task-revision.md). A successful candidate type query does not mean its premises are satisfied or the proof is complete.

**Evidence from Existing Lean Prosa Code**

- Project environment: [lean-toolchain](../../../Deliverables/lean-prosa-v06/lean-toolchain#L1) pins the version; [lakefile.lean](../../../Deliverables/lean-prosa-v06/lakefile.lean#L7) pins the Mathlib commit and declares the Prosa/CaseStudies libraries. Compilation and queries after migration use this package, `Deliverables/lean-prosa-v06/` ([TARGET_ENVIRONMENT](../../TARGET_ENVIRONMENT.md)); `Prosa-Shunqi/` is only the development workspace it was exported from.
- Parameters: [JobType and JobCost](../../../Deliverables/lean-prosa-v06/Prosa/Behavior/Job.lean#L24) use a type carrier and `[DecidableEq Job]`; applications cannot be generated solely from original Coq lemma names.
- Bool/Prop: [completed_by](../../../Deliverables/lean-prosa-v06/Prosa/Behavior/Service.lean#L53) returns Bool; the proof of [basic_readiness_compliance](../../../Deliverables/lean-prosa-v06/Prosa/Analysis/Facts/Readiness/Basic.lean#L57) explicitly handles `pending … = true`. Candidate matching must check actual types and bridging conditions.
- Instances and declaration names: [basic_ready_instance](../../../Deliverables/lean-prosa-v06/Prosa/Model/Readiness/Basic.lean#L20) is a definition not registered globally as an instance; the [corresponding theorem](../../../Deliverables/lean-prosa-v06/Prosa/Analysis/Facts/Readiness/Basic.lean#L47) passes it explicitly. Queries/audits must preserve namespaces, actual binders, and instance context.

**Per-File Documentation**

### 1. Core Proof Tools (6 files)

- [coqc.ts](01-core-tools/coqc-revision.md)
- [coqtop.ts](01-core-tools/coqtop-revision.md)
- [coq-session.ts](01-core-tools/coq-session-revision.md)
- [petanque.ts](01-core-tools/petanque-revision.md)
- [checkpoint.ts](01-core-tools/checkpoint-revision.md)
- [proof-plan.ts](01-core-tools/proof-plan-revision.md)

### 2. Adapted OpenCode Tools (8 files)

- [read.ts](02-adapted-tools/read-revision.md)
- [edit.ts](02-adapted-tools/edit-revision.md)
- [write.ts](02-adapted-tools/write-revision.md)
- [multiedit.ts](02-adapted-tools/multiedit-revision.md)
- [apply_patch.ts](02-adapted-tools/apply_patch-revision.md)
- [bash.ts](02-adapted-tools/bash-revision.md)
- [task.ts](02-adapted-tools/task-revision.md)
- [lsp.ts](02-adapted-tools/lsp-revision.md)

### 3. Custom Tools (1 file; 5 unused custom tools removed 2026-10-09, see ../GAPS.md §8)

- [coq-check.ts](03-custom-tools/coq-check-revision.md)

### 4. Internal Tool Helpers (11 files)

- [coq-project.ts](04-helper-modules/coq-project-revision.md)
- [coq-diagnostics.ts](04-helper-modules/coq-diagnostics-revision.md)
- [coq-style-guard.ts](04-helper-modules/coq-style-guard-revision.md)
- [coq-skill-hints.ts](04-helper-modules/coq-skill-hints-revision.md)
- [proof-premise-audit.ts](04-helper-modules/proof-premise-audit-revision.md)
- [proof-schema.ts](04-helper-modules/proof-schema-revision.md)
- [coq-ast-audit.ts](04-helper-modules/coq-ast-audit-revision.md)
- [proof-plan-identifiers.ts](04-helper-modules/proof-plan-identifiers-revision.md)
- [edit-conflict-guard.ts](04-helper-modules/edit-conflict-guard-revision.md)
- [registry.ts](04-helper-modules/registry-revision.md)
- [tool.ts](04-helper-modules/tool-revision.md)

### 5. Proof Sessions and Workflow (8 files)

- [proof-workflow.ts](05-session-workflow/proof-workflow-revision.md)
- [proof-edit-transaction.ts](05-session-workflow/proof-edit-transaction-revision.md)
- [proof-projection.ts](05-session-workflow/proof-projection-revision.md)
- [proof-context.ts](05-session-workflow/proof-context-revision.md)
- [proof-policy.ts](05-session-workflow/proof-policy-revision.md)
- [lemma-assignment.ts](05-session-workflow/lemma-assignment-revision.md)
- [session-proof.ts](05-session-workflow/session-proof-revision.md)
- [proof-route-ledger.ts](05-session-workflow/proof-route-ledger-revision.md)

### 6. Session Persistence Schemas (4 files)

- [proof-edit-transaction.sql.ts](06-session-storage/proof-edit-transaction.sql-revision.md)
- [proof-route-ledger.sql.ts](06-session-storage/proof-route-ledger.sql-revision.md)
- [session-proof-workflow.sql.ts](06-session-storage/session-proof-workflow.sql-revision.md)
- [session-proof.sql.ts](06-session-storage/session-proof.sql-revision.md)

### 7. LSP Interfaces and Configuration (4 files)

- [index.ts](07-lsp/index-revision.md)
- [client.ts](07-lsp/client-revision.md)
- [server.ts](07-lsp/server-revision.md)
- [language.ts](07-lsp/language-revision.md)
