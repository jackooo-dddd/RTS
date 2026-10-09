# Lean 4 Migration Notes for `petanque.ts`

**Purpose**: Execute tactics, retrieve proof goals, and manage state handles through the Rocq LSP Petanque interface.

**Backend (decided 2026-10-09):** merge this tool into the Pantograph-backed session tool (one interactive tool, not two) — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**1. Petanque Protocol and State Handles | Rewrite, Large**

- **Location**: [Line 14](../../../prosabuddy-rocq/packages/opencode/src/tool/petanque.ts#L14).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Petanque state structure, [From line 14](../../../prosabuddy-rocq/packages/opencode/src/tool/petanque.ts#L14):

```ts
interface PetanqueSession {
  id: string
  uri: string
  state: number | null
  theorem: string
  history: { tac: string; state: number }[]
```

Petanque start request, [From line 80](../../../prosabuddy-rocq/packages/opencode/src/tool/petanque.ts#L80):

```ts
          const result = await LSP.rocqPetanqueStart({
            file,
            theorem: params.theorem,
          })
          state = result.st
```

- **Current behavior**: Stores a numeric `state`; start/run/goals call `rocqPetanqueStart/Run/Goals` and read `st`, feedback, and `proof_finished`.
- **Recommendation**: Connect a Lean session backend and remap state handles, execution results, and errors; Petanque request names cannot simply be sent to Lean LSP. If consolidating with Lean session, remove this tool's old registration while retaining interactive capabilities.

**2. Goal Rendering and Input Guidance | Modify, Medium**

- **Location**: [Line 212: formatGoals](../../../prosabuddy-rocq/packages/opencode/src/tool/petanque.ts#L212).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq goal data structure, [From line 212](../../../prosabuddy-rocq/packages/opencode/src/tool/petanque.ts#L212):

```ts
function formatGoals(goals: { goals: { hyps: { names: string[]; ty: string }[]; ty: string }[] }): string {
  if (goals.goals.length === 0) return "No goals"

  const parts: string[] = []
  for (let i = 0; i < goals.goals.length; i++) {
```

Embedded tool description, [From line 28](../../../prosabuddy-rocq/packages/opencode/src/tool/petanque.ts#L28):

```ts
const DESCRIPTION = `Petanque: Interact with Rocq/Coq proofs through LSP using single-step execution.

This tool provides a more efficient alternative to coq_session for proof development,
using rocq-lsp's Petanque API for incremental tactic execution.
```

- **Current behavior**: Assumes goals have the form `{hyps: {names,ty}[], ty}`; the embedded DESCRIPTION and run guards are Coq-specific.
- **Recommendation**: Use Lean's local-context and goal formats; remove Coq tactic guards and update `.v` and Petanque wording. Empty goals mean only that the current state has no goals, not that final file validation is certified.

Operation dispatch and the session-history wrapper can be reused; whether to retain a separate tool depends on the Lean session backend.
