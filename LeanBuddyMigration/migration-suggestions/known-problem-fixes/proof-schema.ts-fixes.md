# Fixes: `tool/proof-schema.ts`

**File**: [`tool/proof-schema.ts`](../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts). **Implements**: DECISIONS D9, D10.

| Location | Change |
|---|---|
| [#L185](../../prosabuddy-rocq/packages/opencode/src/tool/proof-schema.ts#L185) `MAX_SEMANTIC_PLAN_REVISIONS = 4` | keep; add `MAX_PLAN_AMENDMENTS = 3` next to it (D9). |
| plan-node schema (`ProofPlanStep`) | add the `Amendment` object (`node`, `depends_on`, `inserts_before`, `addresses_escalation`); `normal_form` documented as "a Lean proposition in the theorem's context" (D10). |
| region-marker fields | required: `owner`, `admit_id`, `theorem`, `target`, `plan_node`; `kind`/`layer` are no longer carried (owned by the plan node, D10). Contract fields and evidence prefixes: DECISIONS D10, D13. |
