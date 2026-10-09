# Lean 4 Migration Notes for `proof-projection.ts`

**Purpose**: Generate proof context and working instructions according to the agent's role and proof state.

**1. Staged Source and Goal State | Modify, Medium**

- **Location**: [Line 37: stagedLemmaContext](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L37).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq guidance in staged context, [Line 93](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L93):

```ts
      "The rocq-lsp snapshot is intentionally suppressed because it would be computed from the older physical file and may name a sibling goal. Use the assigned goal as the entry contract and region-scoped `coq_session` for exact intermediate goals.",
```

- **Current behavior**: Suppresses old Rocq LSP snapshots when staged content differs from disk and directs the agent to coq_session for local context.
- **Recommendation**: Retain the flow that prevents stale snapshots from misleading the agent; read Lean goals corresponding to the staged revision and update tool instructions in `stagedLemmaReminder`.

**2. Proof Structure and Tactic Instructions | Rewrite, Medium**

- **Location**: [Line 98: prover](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L98).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Declaration-structure instructions for prover, [From line 113](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L113):

```ts
      "4. Represent paper-relevant objects, sets, abbreviations, notations, and expressions as `pose` or `set`. Represent paper-relevant claims, cases, rewrites, bounds, contradictions, and derived consequences as `have` or `assert`.",
      "5. If one proposed region crosses independent semantic claims or dependency boundaries, split it at a useful intermediate Coq proposition; do not split merely because one coherent fact needs several local proof steps.",
```

Coq tool and style instructions for lemma, [From line 237](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L237):

```ts
      "- After the informal proof, open and use `coq_session` or `petanque` for atomic tactics, goal queries, snapshots, and rollback whenever possible.",
      "- Use `lsp proofGoals` and edit/write LSP diagnostics as first-class proof feedback; use `coqc` at coherent milestones and before returning.",
      "- Use `coqtop`/`grep`/broad reads only for a blocker exposed by the current goal or failed step, and immediately feed the result into an edit, proof-session step, or rollback decision.",
      "- Do not use ssreflect repeat-rewrite syntax `rewrite !...` or `rewrite -!...`; write repeated rewrites explicitly one step at a time, or introduce a named normalization/bridge lemma.",
      "- Do not use the `intuition` tactic; it generates opaque proof terms and is rejected. Use explicit tactics (`left`/`right`/`split`/`apply`/`exact`) instead.",
```

- **Current behavior**: Instructions for prover/lemma/fixer/wholeLemma include pose/have, Coq braces, Section, Qed/Admitted, SSReflect restrictions, and Coq tool names.
- **Recommendation**: Rewrite using Lean local `have … := by`, indentation ranges, and actual tool capabilities; inspect Lean parameters and instance context, and remove Coq tactic bans and terminator-editing instructions.

**3. Paper Mapping and Layer Terminology | Modify, Small**

- **Location**: [Line 396: faithful](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L396).

**Source code to adapt**:

`prover` branch, [Line 402](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L402):

```ts
        "3. Annotate each theorem-level pose/have with its paper mapping or context-derived source and its role in the proof DAG.",
```

`lemma` branch, [From line 411](../../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L411):

```ts
        "3. Use that informal proof as the controlling local proof plan; if it is not precise enough, refine it before touching the Coq proof.",
        "4. Insert a local annotated pose/have skeleton only when the informal proof itself requires that local decomposition.",
```

- **Current behavior**: Paper mode uses `Coq proof` and `pose/have` to describe proofs and local decomposition skeletons.
- **Recommendation**: Replace `Coq proof` with `Lean proof`, and describe `pose/have` skeletons using Lean local definitions or `have … := by` subproofs; retain paper mapping, local task boundaries, and escalation rules.

The mechanism for tailoring context and responsibilities to roles such as prover/lemma/fixer/explorer can be retained.
