# Lean migration review — recommendations only

All eight original skills, their metadata values, rules and Rocq examples are retained. Red English annotations describe possible future changes; gray text identifies original passages under review. No Lean migration, skill deletion or code replacement has been applied.

| Skill | Recommendation for a future Lean version |
|---|---|
| [count-bridging](count-bridging/SKILL.md) | Keep representation normalization before arithmetic. Adapt the bridges to actual List/Finset or RTS sum APIs. Remove Bool / Prop Separation through Boundary Failure Signs, including the fixed reflection handoff. |
| [failure-signature](failure-signature/SKILL.md) | Defer this lookup skill until real Lean/ProsaBuddy runs support a new diagnostic table. Keep the old table as historical evidence. |
| [goal](goal/SKILL.md) | Keep active-goal and local-proof checks. Replace Coq syntax and diagnostics; remove or redesign Hard Recovery Protocol rather than enforcing exactly one goal. |
| [guide](guide/SKILL.md) | Keep small verified repairs, ownership and proof integrity. Adapt state inspection, proof boundaries and validation to the Lean backend. |
| [math](math/SKILL.md) | Keep goal-driven rewriting and connecting equalities. Replace MathComp identities, templates and diagnostic mappings using actual Lean interfaces and evidence. |
| [parameter](parameter/SKILL.md) | Keep the distinction between unresolved inputs and proof premises. Recheck every Prosa example against the actual RTS theorem signature and instances. |
| [prosabuddy-guard-recovery](prosabuddy-guard-recovery/SKILL.md) | Keep recovery policy, candidate roles, revision management and dependency scheduling. Adapt only backend-specific proof-state, premise-audit and compiler-certificate production and verification. |
| [tactics](tactics/SKILL.md) | Remove this SSReflect-specific skill from the future Lean version. Lean by starts a proof block and must not be deleted to inspect its tactics. Keep general stepwise debugging in guide. |

## What the failure-signature example actually shows

The example concerns adding `num_cpus` copies of the same natural number `X`. After `rewrite big_const_ord.`, it shows a possible goal involving `iter`. **It does not show a failing command or actual error output.** The resulting equality is a proof state, not a diagnostic.

A future lookup table should record the real Lean version and imports, failing source and location, diagnostic, goal and context, confirmed cause, and validated repair. Translating a successful example does not supply that evidence.

## Why the fixed Bool/Prop handoff can go

Ordinary Lean natural-number inequalities are propositions, so this arithmetic stage does not need MathComp reflection and a return to Bool. That particular workflow becomes shorter; it does not imply that every Lean proof is simpler. Actual Bool-valued RTS definitions still need their real interfaces, and List counts must preserve duplicates.

## Reference used for recommendations

The API review used [RTS at commit d577db4](../../../Deliverables/lean-prosa-v06), Lean `4.33.1`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Relevant modules include `Prosa.Util.Sum`, `Prosa.Analysis.Facts.BlockingBound.Fp`, `Prosa.Model.Priority.Coercion` and `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation`.

Exploratory API checks support the recommendations; they are not a completed migration. Recheck declarations against the target checkout before implementing any proposal. Concerns that already exist in Rocq are recorded separately in [Issues in the original skills](SKILL_ISSUES.md).
