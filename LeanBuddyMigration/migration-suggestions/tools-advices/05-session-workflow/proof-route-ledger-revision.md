# Lean 4 Migration Notes for `proof-route-ledger.ts`

**Purpose**: Record failed proof routes and their evidence, using context and premise fingerprints to detect repeated routes.

**1. Theorem Context Fingerprints | Rewrite, Medium**

- **Location**: [Line 209: theoremContextFingerprint](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.ts#L209).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq theorem context discovery, [From line 209](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.ts#L209):

```ts
  export function theoremContextFingerprint(source: string, theorem: string) {
    const masked = maskCommentsAndStrings(source)
    const declaration = new RegExp(
      `\\b(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\\s+${escapeRegExp(theorem)}\\b`,
      "g",
    ).exec(masked)
```

Section and Module scope recognition, [From line 230](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.ts#L230):

```ts
      const open = /^(Section|Module(?:\s+Type)?)\s+([A-Za-z0-9_']+)/.exec(command)
      if (open) {
        frames.push({ name: open[2], header: command, assumptions: [] })
        continue
```

- **Current behavior**: Extracts context using Coq commands such as theorem/Proof, Section/Module, and Variables/Hypotheses.
- **Recommendation**: Use Lean declarations and their namespace, variable, open, and local-instance scopes; changes to parameters or instances should produce different context fingerprints.

**2. Goal and Premise Text Normalization | Modify, Medium**

- **Location**: [Line 150: normalizedText](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.ts#L150).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq comment and case handling, [From line 150](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.ts#L150):

```ts
  function normalizedText(value: string | undefined) {
    return (value ?? "")
      .replace(/\(\*[\s\S]*?\*\)/g, " ")
      .replace(/\s+/g, " ")
      .trim()
      .toLowerCase()
  }
```

- **Current behavior**: Removes Coq comments and lowercases text for goal/premise fingerprints.
- **Recommendation**: Recognize Lean comments and preserve identifier case, binders, and Bool/Prop distinctions; old Coq fingerprints should not directly justify semantic reuse in Lean.

**3. Candidate Route Fields | Modify, Small**

- **Location**: [Line 446: assessKnownRouteReuse](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.ts#L446).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

MathComp candidates in route reuse, [From line 475](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.ts#L475):

```ts
      ...(node.mathcomp_candidate_lemmas ?? []).map((entry) => ({
        ...entry,
        node_id: node.node_id,
        formal_goal: node.formal_goal,
```

- **Current behavior**: Retry checks read `mathcomp_candidate_lemmas` and candidate-audit results.
- **Recommendation**: Use Mathlib fields and instantiation/premise fingerprints produced by Lean audits; retain general route-reuse rules.

Route failure records, evidence references, retry rules, and persistence can be retained.
