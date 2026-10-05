# `implementation/refinements/fast_search_space_computation.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `search_space_arrival_curve_prefix_FP_h` | Definition | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP_h` | `search_space_arrival_curve_prefix_FP_h_correspondence` | [view](3_printed_declarations/search_space_arrival_curve_prefix_FP_h.md) |
| `search_space_arrival_curve_prefix_FP` | Definition | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP` | `search_space_arrival_curve_prefix_FP_correspondence` | [view](3_printed_declarations/search_space_arrival_curve_prefix_FP.md) |
| `steps_lt_horizon_last_eq_horizon` | Lemma | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.steps_lt_horizon_last_eq_horizon` | `steps_lt_horizon_last_eq_horizon_correspondence` | [view](3_printed_declarations/steps_lt_horizon_last_eq_horizon.md) |
| `structure_of_correct_search_space` | Lemma | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.structure_of_correct_search_space` | `structure_of_correct_search_space_correspondence` | [view](3_printed_declarations/structure_of_correct_search_space.md) |
| `multiple_of_horizon_in_approx_ss` | Lemma | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.multiple_of_horizon_in_approx_ss` | `multiple_of_horizon_in_approx_ss_correspondence` | [view](3_printed_declarations/multiple_of_horizon_in_approx_ss.md) |
| `steps_in_approx_ss` | Lemma | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.steps_in_approx_ss` | `steps_in_approx_ss_correspondence` | [view](3_printed_declarations/steps_in_approx_ss.md) |
| `constant_max_arrivals` | Lemma | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.constant_max_arrivals` | `constant_max_arrivals_correspondence` | [view](3_printed_declarations/constant_max_arrivals.md) |
| `task_search_space_subset` | Lemma | `Prosa.Implementation.Refinements.FastSearchSpaceComputation.task_search_space_subset` | `task_search_space_subset_correspondence` | [view](3_printed_declarations/task_search_space_subset.md) |

## Certificates

| Module | Role |
|---|---|
| [`RfsBase`](4_correspondence/RfsBase.v) | Correspondences for `implementation/refinements/refinements.v`. |
| [`RefFastSearchSpaceComputationCorrespondence`](4_correspondence/RefFastSearchSpaceComputationCorrespondence.v) | Correspondences for `implementation/refinements/fast_search_space_computation.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
