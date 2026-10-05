# `results/rta/ideal/edf/bounded_nps.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `is_in_search_space` | Definition | `Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space` | `is_in_search_space_correspondence` | [view](3_printed_declarations/is_in_search_space.md) |
| `blocking_bound_decreasing` | Fact | `Prosa.Results.Rta.Ideal.Edf.BoundedNps.blocking_bound_decreasing` | `blocking_bound_decreasing_correspondence` | [view](3_printed_declarations/blocking_bound_decreasing.md) |
| `task_with_equal_deadline_exists` | Lemma | `Prosa.Results.Rta.Ideal.Edf.BoundedNps.task_with_equal_deadline_exists` | `task_with_equal_deadline_exists_correspondence` | [view](3_printed_declarations/task_with_equal_deadline_exists.md) |
| `search_space_inclusion` | Lemma | `Prosa.Results.Rta.Ideal.Edf.BoundedNps.search_space_inclusion` | `search_space_inclusion_correspondence` | [view](3_printed_declarations/search_space_inclusion.md) |
| `uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments` | Theorem | `Prosa.Results.Rta.Ideal.Edf.BoundedNps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments` | `uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaIdealEdfBoundedNpsCorrespondence`](4_correspondence/RtaIdealEdfBoundedNpsCorrespondence.v) | Main certificate for results/rta/ideal/edf/bounded_nps.v: the helper part (no statement correspondences) of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
