# Lean 4 Migration Notes for `lemma-assignment.ts`

**Purpose**: Define task contracts, proof obligations, context audits, and structured result formats for lemma delegation.

**1. Candidate Library Fields | Modify, Small**

- **Location**: [Line 104: LemmaObligationSchema](../../../prosabuddy-rocq/packages/opencode/src/session/lemma-assignment.ts#L104).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

MathComp candidate field, [Line 118](../../../prosabuddy-rocq/packages/opencode/src/session/lemma-assignment.ts#L118):

```ts
  mathcomp_candidate_lemmas: z.array(z.string()).default([]),
```

- **Current behavior**: Obligations contain `mathcomp_candidate_lemmas` and carry local goals and candidate-audit information.
- **Recommendation**: Rename to Mathlib fields together with proof-schema/workflow; use actual names and parameters for Lean Prosa candidates.

**2. Context Audits and Task Descriptions | Modify, Medium**

- **Location**: [Line 46: ContextMismatchBasis](../../../prosabuddy-rocq/packages/opencode/src/session/lemma-assignment.ts#L46).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Context-mismatch classification, [From line 46](../../../prosabuddy-rocq/packages/opencode/src/session/lemma-assignment.ts#L46):

```ts
export const ContextMismatchBasis = z.enum([
  "hidden_arguments",
  "section_context",
  "module_instantiation",
  "implicit_arguments",
  "alias_normalization",
  "other",
```

Coq file description, [Line 148](../../../prosabuddy-rocq/packages/opencode/src/session/lemma-assignment.ts#L148):

```ts
    file: z.string().min(1).describe("Workspace-relative Coq file path containing the assigned proof_region to replace or update"),
```

- **Current behavior**: Context-failure categories include section_context and module_instantiation; `LemmaAssignmentSchema` describes the target file as Coq source.
- **Recommendation**: Adjust categories and descriptions to the meanings of Lean namespace/section, variable, implicit parameters, and instance synthesis; Coq module instantiation is not equivalent to Lean namespaces. Retain general fields such as region IDs and replacement text.

Delegation identity, regions, parent-child relationships, structured results, and failure reports can mostly be retained.
