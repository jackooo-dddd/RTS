# Revision: `cli/cmd/run.ts` (non-interactive `opencode run`, used by the benchmark runner)

**File**: [`cli/cmd/run.ts`](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts) (740 lines). **Change size**: Modify, Small. **Follows**: DECISIONS D2.

| Lines | Current | Change |
|---|---|---|
| [#L24-L25](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts#L24) | imports `CoqcTool`, `CoqtopTool` | import `LeanCheckTool`, `LeanQueryTool` (and `LeanSessionTool` if a renderer is added). |
| [#L75-L79](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts#L75) | `looksLikeCoqProofBenchmarkPrompt`: `(Coq\|Rocq) … theorem-proving`, "target file … .v", "`coqc X.v`" | `looksLikeLeanProofBenchmarkPrompt`: `Lean … theorem-proving`, "target file … .lean", "`lake env lean X.lean`" / "`lean_check X.lean`". The result selects the `prover` agent (L339). |
| [#L154-L168](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts#L154) | inline renderers `coqc(...)` ("coqc FILE: ok/fail") and `coqtop(...)` | `lean_check(...)` ("lean_check FILE: ok/fail") and `lean_query(...)`; add a one-line renderer for `lean_session` (operation + resulting goal count). |
| [#L406-L407](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts#L406) | dispatch `part.tool === "coqc"` / `"coqtop"` | `"lean_check"` / `"lean_query"` (/ `"lean_session"`). |

Output only (terminal rendering and agent auto-selection); no proof logic lives here.
