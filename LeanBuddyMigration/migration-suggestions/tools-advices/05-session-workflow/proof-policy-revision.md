# Lean 4 Migration Notes for `proof-policy.ts`

**Purpose**: Define proof-progress, region-delivery, and completion requirements for the main prover and lemma subagents.

**1. Main Proof Completion Requirements | Modify, Small**

- **Location**: [Line 7: proverTheoremWorkflowPrompt](../../../prosabuddy-rocq/packages/opencode/src/session/proof-policy.ts#L7).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Final proof-closing instruction, [Line 17](../../../prosabuddy-rocq/packages/opencode/src/session/proof-policy.ts#L17):

```ts
    "After all regions are compiler-certified, compose them in the parent and replace the theorem terminator with Qed only after final validation.",
```

- **Current behavior**: Requires final closure with Qed and permits replacing the theorem terminator at the end.
- **Recommendation**: Require the target Lean declaration to pass checking with no unfinished-proof dependencies; remove the terminator-replacement step.

**2. Local Proof Delivery Requirements | Modify, Small**

- **Location**: [Line 22: lemmaLocalProofPrompt](../../../prosabuddy-rocq/packages/opencode/src/session/proof-policy.ts#L22).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Local proof-block structure constraint, [Line 27](../../../prosabuddy-rocq/packages/opencode/src/session/proof-policy.ts#L27):

```ts
    "Work on the first unresolved local proof block. Preserve its braces, edit from the authoritative staged revision, and validate after meaningful proof changes before advancing to later local blocks.",
```

Coq terminator restrictions, [Line 30](../../../prosabuddy-rocq/packages/opencode/src/session/proof-policy.ts#L30):

```ts
    "Do not edit Admitted./Qed. or close the outer theorem. Return solved only with the complete hole-free assigned proof_region and the required structured proof_result.",
```

- **Current behavior**: Requires preserving local braces and prohibits changes to theorem terminators such as Admitted/Qed.
- **Recommendation**: Preserve the Lean region's target and indentation scope and submit only the authorized proof block; do not change outer declarations or introduce new unauthorized assumptions.

The prover/lemma division of responsibilities and existing proof-progress rules can be retained.
