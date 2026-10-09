# Lean 4 Migration Notes for `coq-skill-hints.ts`

**Purpose**: Match Coq error messages to relevant proof skills and repair hints.

**1. Coq Error Patterns and Skill Guidance | Rewrite, Medium**

- **Location**: [Line 10: coqSkillHintsFor](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-skill-hints.ts#L10).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

MathComp error patterns, [From line 43](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-skill-hints.ts#L43):

```ts
      /big_mkcond|sum1_count|big_filter|count_exceeding|nat\.min|minn|if .* then 1 else 0/,
    ) ||
    (has(text, /\bcount\b|\bfilter\b/) && has(text, /does not match any subterm|lhs of|unable to unify|cannot rewrite|rewrite|bigop|\\sum_|\bsum_/))
```

Corresponding Coq skill hint, [From line 48](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-skill-hints.ts#L48):

```ts
      "ssreflect-count-bridging",
      "indicator sums, filtered big operators, counts, and min-bounds may be drifting across incompatible shapes; stabilize the branch with big_mkcond and sum1_count style bridges before the final arithmetic step",
```

- **Current behavior**: Matches Coq scenarios involving SSReflect, bigop, minn, and eapply, and returns Coq skill names and proof guidance.
- **Recommendation**: Rebuild hints using actual Lean diagnostics; reference Lean skills/documentation that exist in the project, and remove brace, Section, and SSReflect-specific guidance.

The mechanism mapping errors to optional hints can be retained.
