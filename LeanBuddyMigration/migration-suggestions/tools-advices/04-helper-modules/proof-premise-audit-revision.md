# Lean 4 Migration Notes for `proof-premise-audit.ts`

**Purpose**: Check whether candidate lemmas can be used in the target context and record residual premises and audit results.

**1. Source Context for Candidate Checking | Rewrite, Large**

- **Location**: [Line 72: theoremProbeContext](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L72).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq theorem declaration lookup, [From line 76](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L76):

```ts
  const declaration = new RegExp(
    `\\b(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\\s+${escaped}\\b`,
  ).exec(masked)
```

Proof entry-point lookup, [From line 81](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L81):

```ts
  const proof = /\bProof\s*\./.exec(tail)
  if (!proof || proof.index === undefined) return undefined
  const proofStart = declaration.index + proof.index
```

- **Current behavior**: Masks Coq comments/strings, identifies theorem and Proof entry points, and constructs probe scripts.
- **Recommendation**: Use Lean declaration ranges and elaboration context, preserving namespace, open, variable, local instances, and imports; copying theorem text alone is insufficient to restore candidate visibility.

**2. Validating Availability and Applicability | Rewrite, Large**

- **Location**: [Line 109: auditCandidateLemma](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L109).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Candidate type query, [From line 134](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L134):

```ts
  const script = [
    context.prefix,
    "Set Printing Implicit.",
    `Check ${input.candidate.name}.`,
    "Goal True.",
```

Candidate application probe, [From line 152](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L152):

```ts
    directApplication ? `    eapply ${input.candidate.name}.` : undefined,
    directApplication ? "    all: try assumption." : undefined,
    directApplication ? "    all: try reflexivity." : undefined,
```

- **Current behavior**: Generates `Check`; the direct_apply branch probes using assert/intros/eapply and assumption/reflexivity, while other roles mainly confirm name availability.
- **Recommendation**: Replace Check with Lean name resolution and type checking; for direct_apply, execute apply/refine in the actual target and context and collect remaining goals. Retain the distinction between name availability and target applicability: successful `#check` does not establish conclusion compatibility.

**3. Residual Premises and Instantiation Results | Rewrite, Large**

- **Location**: [Line 95: residualGoals](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L95).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Residual-premise parser, opening lines, [From line 95](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L95):

```ts
function residualGoals(output: string, marker: string) {
  const beforeDone = output.split(`${marker}_DONE`)[0] ?? output
  return beforeDone
    .split(`${marker}_RESIDUAL`)
    .slice(1)
    .map(normalize)
```

- **Current behavior**: Extracts residual premises and types from idtac markers and Coq goal text, then computes instantiation fingerprints.
- **Recommendation**: Read Lean goal expressions and local context, preserving implicit parameters, instance parameters, and unresolved metavariables. Check Lean Prosa Bool observations, Prop propositions, and `DecidableEq` constraints against their actual types; failed typeclass search must not be treated as an already satisfied premise.

**4. MathComp Candidate Entry Point | Modify, Small**

- **Location**: [Line 238: auditPlanLibraryCandidates](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L238).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Library candidate classification, [From line 249](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-premise-audit.ts#L249):

```ts
    const candidates = [
      ...(node.prosa_candidate_lemmas ?? []).map((candidate) => ({ kind: "prosa" as const, candidate })),
      ...(node.mathcomp_candidate_lemmas ?? []).map((candidate) => ({ kind: "mathcomp" as const, candidate })),
    ]
```

- **Current behavior**: Traverses prosa and mathcomp candidate lists and invokes the same audit function.
- **Recommendation**: Update to Mathlib candidates together with the schema; use fully qualified translated declaration names and actual parameters for Prosa candidates, retaining the existing scheduling flow.

Candidate-audit scheduling, concurrency limits, attaching results to the plan, and fingerprint organization can be retained.

**Lean code references**: [Type and instance parameters](../../../../Deliverables/lean-prosa-v06/Prosa/Behavior/Job.lean#L24); [Explicit instances and Bool premises](../../../../Deliverables/lean-prosa-v06/Prosa/Analysis/Facts/Readiness/Basic.lean#L57).
