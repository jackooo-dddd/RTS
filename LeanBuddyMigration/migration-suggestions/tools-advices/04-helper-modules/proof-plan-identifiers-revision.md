# Lean 4 Migration Notes for `proof-plan-identifiers.ts`

**Purpose**: Normalize proof DAG node IDs, aliases, dependency references, and candidate-lemma premise-source references.

**1. Candidate Field Traversal | Modify, Small**

- **Location**: [Line 74](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan-identifiers.ts#L74).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

MathComp candidate premise references, [From line 74](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan-identifiers.ts#L74):

```ts
    mathcomp_candidate_lemmas: (node.mathcomp_candidate_lemmas ?? []).map((candidate) => ({
      ...candidate,
      premise_sources: (candidate.premise_sources ?? []).map((source) => ({
        ...source,
        dependency_node: source.dependency_node ? resolve(source.dependency_node) : undefined,
```

- **Current behavior**: Accesses MathComp candidate fields while normalizing candidate `premise_sources.dependency_node` references.
- **Recommendation**: Rename them to Mathlib fields together with the schema. Machine node IDs are not Lean declaration names, so their slug rules need not be rewritten for Unicode declarations.

Machine node IDs, aliases, and dependency-reference normalization can all be retained.
