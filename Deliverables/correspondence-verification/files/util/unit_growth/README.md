# `util/unit_growth.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `unit_growth_function` | Definition | `Prosa.Util.UnitGrowth.unit_growth_function` | `ug_unit_growth_correspondence` | [view](3_printed_declarations/unit_growth_function.md) |
| `unit_growth_function_k_steps_bounded` | Lemma | `Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded` | `unit_growth_function_k_steps_bounded_statement_certificate` | [view](3_printed_declarations/unit_growth_function_k_steps_bounded.md) |
| `exists_intermediate_point` | Lemma | `Prosa.Util.UnitGrowth.exists_intermediate_point` | `exists_intermediate_point_statement_certificate` | [view](3_printed_declarations/exists_intermediate_point.md) |
| `exists_intermediate_point_leq` | Corollary | `Prosa.Util.UnitGrowth.exists_intermediate_point_leq` | `exists_intermediate_point_leq_statement_certificate` | [view](3_printed_declarations/exists_intermediate_point_leq.md) |
| `exists_first_intermediate_point` | Lemma | `Prosa.Util.UnitGrowth.exists_first_intermediate_point` | `exists_first_intermediate_point_statement_certificate` | [view](3_printed_declarations/exists_first_intermediate_point.md) |
| `slowed` | Fixpoint | `Prosa.Util.UnitGrowth.slowed` | `ug_slowed_correspondence` | [view](3_printed_declarations/slowed.md) |
| `slowed_respects_pointwise_leq` | Lemma | `Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq` | `slowed_respects_pointwise_leq_statement_certificate` | [view](3_printed_declarations/slowed_respects_pointwise_leq.md) |
| `slowed_is_unit_step` | Lemma | `Prosa.Util.UnitGrowth.slowed_is_unit_step` | `slowed_is_unit_step_statement_certificate` | [view](3_printed_declarations/slowed_is_unit_step.md) |
| `slowed_respects_monotone` | Lemma | `Prosa.Util.UnitGrowth.slowed_respects_monotone` | `slowed_respects_monotone_statement_certificate` | [view](3_printed_declarations/slowed_respects_monotone.md) |
| `slowed_never_exceeds` | Lemma | `Prosa.Util.UnitGrowth.slowed_never_exceeds` | `slowed_never_exceeds_statement_certificate` | [view](3_printed_declarations/slowed_never_exceeds.md) |
| `bound_preserved_under_slowed` | Corollary | `Prosa.Util.UnitGrowth.bound_preserved_under_slowed` | `bound_preserved_under_slowed_statement_certificate` | [view](3_printed_declarations/bound_preserved_under_slowed.md) |
| `slowed_subtraction_value_preservation` | Lemma | `Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation` | `slowed_subtraction_value_preservation_statement_certificate` | [view](3_printed_declarations/slowed_subtraction_value_preservation.md) |

## Certificates

| Module | Role |
|---|---|
| [`UnitGrowthCertificate`](4_correspondence/UnitGrowthCertificate.v) | Exact target-type guards. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `SubNatTrue`, `True`, `UgTruth`, `eq`, `eq_inst1` |
| Rocq primitives | — |
