# `analysis/facts/preemption/task/nonpreemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions` | Lemma | `Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions` | `fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence` | [view](3_printed_declarations/fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions.md) |
| `fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions` | Corollary | `Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions` | `fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence` | [view](3_printed_declarations/fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsTaskNonpreemptiveCorrespondence`](4_correspondence/FactsTaskNonpreemptiveCorrespondence.v) | Statement correspondences for `analysis/facts/preemption/task/nonpreemptive.v`: the extracted statements (elaborated with the source's section-local fully nonpreemptive job/task instances) against … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
