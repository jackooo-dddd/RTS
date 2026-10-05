# `results/rta/ideal/fifo/bounded_nps.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `abstractly_work_conserving` | Fact | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.abstractly_work_conserving` | `abstractly_work_conserving_correspondence` | [view](3_printed_declarations/abstractly_work_conserving.md) |
| `busy_windows_are_bounded` | Fact | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.busy_windows_are_bounded` | `busy_windows_are_bounded_correspondence` | [view](3_printed_declarations/busy_windows_are_bounded.md) |
| `no_priority_inversion` | Lemma | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.no_priority_inversion` | `no_priority_inversion_correspondence` | [view](3_printed_declarations/no_priority_inversion.md) |
| `IBF_correct` | Lemma | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.IBF_correct` | `IBF_correct_correspondence` | [view](3_printed_declarations/IBF_correct.md) |
| `is_in_concrete_search_space` | Definition | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space` | `is_in_concrete_search_space_correspondence` | [view](3_printed_declarations/is_in_concrete_search_space.md) |
| `search_space_refinement` | Lemma | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.search_space_refinement` | `search_space_refinement_correspondence` | [view](3_printed_declarations/search_space_refinement.md) |
| `soln_abstract_response_time_recurrence` | Lemma | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.soln_abstract_response_time_recurrence` | `soln_abstract_response_time_recurrence_correspondence` | [view](3_printed_declarations/soln_abstract_response_time_recurrence.md) |
| `uniprocessor_response_time_bound_FIFO` | Theorem | `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.uniprocessor_response_time_bound_FIFO` | `uniprocessor_response_time_bound_FIFO_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_FIFO.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaIdealFifoBoundedNpsCorrespondence`](4_correspondence/RtaIdealFifoBoundedNpsCorrespondence.v) | Main certificate for results/rta/ideal/fifo/bounded_nps.v: the helper part (no statement correspondences) of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
