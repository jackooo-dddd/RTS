# Lean 4 Migration Notes for `proof-plan.ts`

**Purpose**: Build and review proof DAGs, managing subgoal decomposition, dependencies, and candidate-lemma premise audits.

**1. Bound File Type | Modify, Small**

- **Location**: [Line 787: boundProofFile](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L787) (inside `execute`).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Bound file type, [From line 787](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L787):

```ts
    const boundProofFile = Boolean(
      binding?.file.endsWith(".v") && (await Filesystem.exists(binding.file)),
    )
    if (boundProofFile && binding) {
```

- **Current behavior**: Uses `binding?.file.endsWith(".v")` to decide whether to enter theorem binding, candidate auditing, and plan persistence.
- **Change**: Use `.lean` in the Lean version. [Line 797: theoremTargetAtProofPosition](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L797) and [Line 811: auditPlanLibraryCandidates](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L811) must connect to Lean implementations; retain the call flow here. Dependency internals are outside this document's scope.

**2. Coq Syntax Handling in Goal Text | Modify, Medium**

- **Location**: [Line 163: normalizeGoal](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L163).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq comment and period handling, [From line 163](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L163):

```ts
function normalizeGoal(text: string | undefined) {
  return (text ?? "")
    .replace(/\(\*[\s\S]*?\*\)/g, " ")
    .trim()
    .replace(/\.\s*$/, "")
    .replace(/[{}()]/g, " ")
```

- **Current behavior**: Removes `(* … *)` comments and trailing periods, and normalizes parentheses, binder colons, and whitespace.
- **Change**: Handle Lean `--` and nested `/- … -/` comments instead; remove Coq command-terminating period handling. Normalization must preserve Lean parameter delimiters, implicit parameters, and instance binders, such as `(x : α)`, `{x : α}`, and `[DecidableEq α]`.
- **Affected locations**: [canonicalPlan](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L186), [reviewProofPlan](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L493), and [reviewCompositionDataflow](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L314) all use this function and should consistently use the new goal-text handling.

**3. Lean Declaration Names and Reference Recognition | Modify, Medium**

- **Location**: [Line 242: referenceKeys](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L242); [Line 259: exportedReferenceKeys](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L259).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Declaration reference recognition, [From line 246](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L246):

```ts
  const identifier = (text ?? "").trim().match(/^([A-Za-z_][A-Za-z0-9_']*)\s*(?::|$)/)?.[1]
  if (identifier) keys.add(identifier.toLowerCase())
```

- **Current behavior**: Extracts reference names using `[A-Za-z_][A-Za-z0-9_']*` and converts them to lowercase.
- **Change**: Support Lean Unicode identifiers, qualified names, and escaped identifiers, such as `hα`, `Prosa.Behavior.Service.completed_by`, and `«name»`, while preserving declaration-name case. Update case handling in `normalizeGoal` accordingly; machine node ID formatting need not change.

**4. MathComp Candidate Fields | Modify, Small–Medium**

- **Location**: `mathcomp_candidate_lemmas` at [Line 589](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L589), [Line 602](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L602), [Line 761](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L761), [Line 906](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L906), and [Line 949](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L949).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

MathComp field in candidate review, [From line 602](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L602):

```ts
    for (const candidate of [...(node.prosa_candidate_lemmas ?? []), ...(node.mathcomp_candidate_lemmas ?? [])]) {
      const audit = candidate.audit
      if (!candidate.role) {
```

- **Current behavior**: This field participates in evidence aggregation, candidate review, draft initialization, premise-certificate checks, and failed-route retry checks.
- **Change**: Consistently use `mathlib_candidate_lemmas` in the Lean version, updating all five accesses and the external schema contract. Retain `prosa_candidate_lemmas` for Lean Prosa candidates; this file does not translate individual MathComp lemmas into Mathlib lemmas.

**5. Coq-Specific Descriptions and Diagnostics | Modify, Small**

- **Location**: [Line 30: Parameters field description](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L30); composition-review messages at [Line 335](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L335) and [Line 443](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L443); [Line 620: candidate audit message](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L620); [Line 764: extractNodes.done_when](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L764); [Line 778: tool description](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L778).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq goal parameter description, [Line 30](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L30):

```ts
    root_goal: z.string().optional().describe("The exact theorem goal or its stable Coq-shaped summary."),
```

Candidate audit description, [Line 620](../../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L620):

```ts
            `Library candidate ${candidate.name} has no mechanical Check/application premise audit yet.`,
```

- **Current behavior**: Uses wording such as `Coq-shaped`, `editing Coq`, `validated by Coq`, and `Check/application premise audit`.
- **Change**: Refer to Lean goals, Lean proof editing, Lean validation, and candidate type/application checks, removing references specific to Coq's `Check` command. Retain the messages' purposes and review conditions.

The DAG, dependency management, decomposition rules, candidate roles, plan fingerprint organization, revision budgets, and state management are not Coq-specific migration points in this file and can be retained.
