# `results/rta/ideal/edf/bounded_pi.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_rbf_changes_at` | Definition | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.task_rbf_changes_at` | `task_rbf_changes_at_correspondence` | [view](3_printed_declarations/task_rbf_changes_at.md) |
| `bound_on_total_hep_workload_changes_at` | Definition | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.bound_on_total_hep_workload_changes_at` | `bound_on_total_hep_workload_changes_at_correspondence` | [view](3_printed_declarations/bound_on_total_hep_workload_changes_at.md) |
| `priority_inversion_changes_at` | Definition | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.priority_inversion_changes_at` | `priority_inversion_changes_at_correspondence` | [view](3_printed_declarations/priority_inversion_changes_at.md) |
| `is_in_search_space` | Definition | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.is_in_search_space` | `is_in_search_space_correspondence` | [view](3_printed_declarations/is_in_search_space.md) |
| `instantiated_task_interference_is_bounded` | Lemma | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.instantiated_task_interference_is_bounded` | `instantiated_task_interference_is_bounded_correspondence` | [view](3_printed_declarations/instantiated_task_interference_is_bounded.md) |
| `A_is_in_concrete_search_space` | Lemma | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.A_is_in_concrete_search_space` | `A_is_in_concrete_search_space_correspondence` | [view](3_printed_declarations/A_is_in_concrete_search_space.md) |
| `correct_search_space` | Corollary | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.correct_search_space` | `correct_search_space_correspondence` | [view](3_printed_declarations/correct_search_space.md) |
| `uniprocessor_response_time_bound_edf` | Theorem | `Prosa.Results.Rta.Ideal.Edf.BoundedPi.uniprocessor_response_time_bound_edf` | `uniprocessor_response_time_bound_edf_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_edf.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaIdealEdfBoundedPiCorrespondence`](4_correspondence/RtaIdealEdfBoundedPiCorrespondence.v) | Main certificate for results/rta/ideal/edf/bounded_pi.v: the helper part (no statement correspondences) of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
