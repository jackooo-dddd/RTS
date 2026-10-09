# Lean 4 Migration Notes for `proof-schema.ts`

**Purpose**: Define data structures for proof plans, candidate-lemma audits, project context, interactive sessions, and checkpoints.

**1. Library and Semantic-Layer Enums | Modify, Small–Medium**

- **Location**: [Line 5: ProofPlanLayer](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L5).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Language-specific proof-plan layers, [From line 9](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L9):

```ts
  "prosa",
  "mathcomp",
  "coq_shape",
  "local_arithmetic",
```

Candidate library enum, [Line 63](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L63):

```ts
  library: z.enum(["prosa", "mathcomp", "local", "unknown"]),
```

MathComp candidate field, [Line 150](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L150):

```ts
  mathcomp_candidate_lemmas: z.array(ProofPlanCandidateLemma).default([]),
```

- **Current behavior**: Includes mathcomp and coq_shape layers, MathComp library/source enums, and `mathcomp_candidate_lemmas`.
- **Recommendation**: Consistently replace these with Mathlib/Lean fields and enums and update callers; if old plans must remain readable, handle legacy fields explicitly rather than treating old Coq audits as Lean audits.

**2. Project and Session Structures | Modify, Medium**

- **Location**: [Line 242: CoqProjectContext](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L242).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq project environment fields, [From line 246](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L246):

```ts
  project_path: z.string().nullable(),
  flags: z.array(z.string()),
  cwd: z.string(),
  preamble: z.string(),
```

Session-state structure, opening lines, [From line 265](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L265):

```ts
export const CoqSessionState = z.object({
  session_id: z.string(),
  loaded_file: z.string(),
  focused_goal: z.string(),
  local_hyps: z.array(z.string()),
  tactic_history: z.array(TacticRecord),
```

- **Current behavior**: Projects contain Coq flags/preamble; `CoqSessionState` represents loaded files, goals, local hypotheses, and snapshots.
- **Recommendation**: Represent Lean environment information in the project structure and the selected Lean backend's state references and context in the session structure. Source hash, region, and revision fields can remain; old Coq states cannot be restored directly as Lean sessions.

Most proof DAG, dependency, candidate-audit verdict, checkpoint, and certificate organization structures can be retained.
