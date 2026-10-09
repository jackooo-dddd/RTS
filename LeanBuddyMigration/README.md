# LeanBuddy migration: ProsaBuddy (Rocq) → Lean 4

Entry point. Folder layout:

- [`migration-suggestions/`](migration-suggestions/DECISIONS.md) — every suggestion for translating ProsaBuddy to Lean, one subfolder per kind (below).
- [`prosabuddy-rocq/`](prosabuddy-rocq/BASELINE.md) — the Rocq ProsaBuddy source being translated (pure upstream `8e1de8c`).
- [`TARGET_ENVIRONMENT.md`](TARGET_ENVIRONMENT.md) — the agent, the translated Lean Prosa and case studies, and the Lean environment the Lean version will run on.

Read in this order:

1. [DECISIONS.md](migration-suggestions/DECISIONS.md) — every decision (D1–D14, R1–R7): Pantograph backend, tool names, LSP access, final gate, retry accounting, unused parts dropped, structural fixes.
2. [KNOWN_PROBLEMS.md](migration-suggestions/KNOWN_PROBLEMS.md) — structural problems found in 57 replication runs, each with its decision and fix.
3. [BACKEND_DECISION.md](migration-suggestions/BACKEND_DECISION.md) — Pantograph (interactive), Lean LSP (diagnostics, read-only lookups), `lake build` (final verification).
4. Translation notes, per file:
   - [tools-advices/](migration-suggestions/tools-advices/README.md) — 42 tool/workflow/storage/LSP modules;
   - [prompt-advices/](migration-suggestions/prompt-advices/prompt_revision.md) — the 8 agent prompts;
   - [skill-advices/](migration-suggestions/skill-advices/README.md) — the 8 skills;
   - [gap-revisions/](migration-suggestions/gap-revisions/README.md) — what the notes above did not cover (runtime controller, system prompts, small files, audit backend, runner, tests);
   - [known-problem-fixes/](migration-suggestions/known-problem-fixes/README.md) — fixes applied on top of the translation (D8–D12).
5. [GAPS.md](migration-suggestions/GAPS.md) — record of what was missing and where it is now covered (all items decided).

Code links point at [`prosabuddy-rocq/`](prosabuddy-rocq/BASELINE.md) (pure upstream ProsaBuddy commit `8e1de8c`).

Implementation order: tool names (D2) → final gate (gap-revisions §4) → `lean_session` on Pantograph (BACKEND_DECISION) →
runtime controller, prompts, workflow (tools-advices + gap-revisions §1–3, then known-problem-fixes) → tests with
each module (gap-revisions §7) → benchmark runner last (gap-revisions §5).
