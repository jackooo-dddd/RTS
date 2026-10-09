# LeanBuddy

The Lean 4 port of ProsaBuddy. It proves the Lean Prosa case studies in
[`Deliverables/lean-prosa-v06`](../../Deliverables/lean-prosa-v06/README.md).

- Translated from [`../prosabuddy-rocq/`](../prosabuddy-rocq/BASELINE.md) (pure upstream ProsaBuddy `8e1de8c`), by
  editing a copy of that tree; the layout is unchanged (`packages/opencode/…`, `.opencode/skill/`, `scripts/`).
- How and why: [`../migration-suggestions/DECISIONS.md`](../migration-suggestions/DECISIONS.md) and the task prompt
  [`../AGENT_PROMPT.md`](../AGENT_PROMPT.md); progress and deviations: [`../MIGRATION_LOG.md`](../MIGRATION_LOG.md).
- Backend: Pantograph (interactive goals), Lean LSP (diagnostics, read-only lookups), `lake build` + the benchmark
  gate (final verification) — [`../migration-suggestions/BACKEND_DECISION.md`](../migration-suggestions/BACKEND_DECISION.md).
- Runtime: Bun 1.3.10 (`bun install`, `bun run typecheck`, `bun test` in `packages/opencode`).

The original ProsaBuddy README is kept as [`README.prosabuddy.md`](README.prosabuddy.md).
