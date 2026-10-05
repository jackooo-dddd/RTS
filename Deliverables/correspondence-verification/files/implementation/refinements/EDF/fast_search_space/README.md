# `implementation/refinements/EDF/fast_search_space.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `bound_on_total_hep_workload` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.bound_on_total_hep_workload` | `bound_on_total_hep_workload_correspondence` | [view](3_printed_declarations/bound_on_total_hep_workload.md) |
| `check_point_FP` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.check_point_FP` | `check_point_FP_correspondence` | [view](3_printed_declarations/check_point_FP.md) |
| `blocking_bound_NP` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.blocking_bound_NP` | `blocking_bound_NP_correspondence` | [view](3_printed_declarations/blocking_bound_NP.md) |
| `check_point_NP` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.check_point_NP` | `check_point_NP_correspondence` | [view](3_printed_declarations/check_point_NP.md) |
| `Task` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task` | `Task_source_total, Task_target_total` | [view](3_printed_declarations/Task.md) |
| `Job` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.Job` | `Job_source_total, Job_target_total` | [view](3_printed_declarations/Job.md) |
| `correct_search_space` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.correct_search_space` | `correct_search_space_correspondence` | [view](3_printed_declarations/correct_search_space.md) |
| `search_space_emax_FP_h` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_FP_h` | `search_space_emax_FP_h_correspondence` | [view](3_printed_declarations/search_space_emax_FP_h.md) |
| `search_space_emax_FP` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_FP` | `search_space_emax_FP_correspondence` | [view](3_printed_declarations/search_space_emax_FP.md) |
| `task_search_space_emax_EDF_h` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF_h` | `task_search_space_emax_EDF_h_correspondence` | [view](3_printed_declarations/task_search_space_emax_EDF_h.md) |
| `task_search_space_emax_EDF` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF` | `task_search_space_emax_EDF_correspondence` | [view](3_printed_declarations/task_search_space_emax_EDF.md) |
| `search_space_emax_EDF` | Definition | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_EDF` | `search_space_emax_EDF_correspondence` | [view](3_printed_declarations/search_space_emax_EDF.md) |
| `EDF_ss_generalize_FP_ss` | Lemma | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.EDF_ss_generalize_FP_ss` | `EDF_ss_generalize_FP_ss_correspondence` | [view](3_printed_declarations/EDF_ss_generalize_FP_ss.md) |
| `search_space_subset_EDF` | Lemma | `Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_subset_EDF` | `search_space_subset_EDF_correspondence` | [view](3_printed_declarations/search_space_subset_EDF.md) |

## Certificates

| Module | Role |
|---|---|
| [`ReArrivalCurvePrefix`](4_correspondence/ReArrivalCurvePrefix.v) | Correspondences for `implementation/refinements/arrival_curve_prefix.v`. |
| [`RefEDFFastSearchSpaceCorrespondence`](4_correspondence/RefEDFFastSearchSpaceCorrespondence.v) | Correspondences for `implementation/refinements/EDF/fast_search_space.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
