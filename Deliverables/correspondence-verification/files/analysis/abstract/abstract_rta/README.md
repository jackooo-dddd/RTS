# `analysis/abstract/abstract_rta.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `relative_arrival_time_of_job_is_A` | Definition | `Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A` | `relative_arrival_time_of_job_is_A_correspondence` | [view](3_printed_declarations/relative_arrival_time_of_job_is_A.md) |
| `relative_time_to_reach_rtct` | Definition | `Prosa.Analysis.Abstract.AbstractRta.relative_time_to_reach_rtct` | `relative_time_to_reach_rtct_correspondence` | [view](3_printed_declarations/relative_time_to_reach_rtct.md) |
| `job_arrival_eq_t1_plus_A` | Fact | `Prosa.Analysis.Abstract.AbstractRta.job_arrival_eq_t1_plus_A` | `job_arrival_eq_t1_plus_A_correspondence` | [view](3_printed_declarations/job_arrival_eq_t1_plus_A.md) |
| `relative_arrival_is_bounded` | Fact | `Prosa.Analysis.Abstract.AbstractRta.relative_arrival_is_bounded` | `relative_arrival_is_bounded_correspondence` | [view](3_printed_declarations/relative_arrival_is_bounded.md) |
| `t2_le_arrival_plus_R_1` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.t2_le_arrival_plus_R_1` | `t2_le_arrival_plus_R_1_correspondence` | [view](3_printed_declarations/t2_le_arrival_plus_R_1.md) |
| `job_completed_by_arrival_plus_R_1` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.job_completed_by_arrival_plus_R_1` | `job_completed_by_arrival_plus_R_1_correspondence` | [view](3_printed_declarations/job_completed_by_arrival_plus_R_1.md) |
| `t2_le_arrival_plus_R_2` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.t2_le_arrival_plus_R_2` | `t2_le_arrival_plus_R_2_correspondence` | [view](3_printed_declarations/t2_le_arrival_plus_R_2.md) |
| `job_completed_by_arrival_plus_R_2` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.job_completed_by_arrival_plus_R_2` | `job_completed_by_arrival_plus_R_2_correspondence` | [view](3_printed_declarations/job_completed_by_arrival_plus_R_2.md) |
| `relative_rtc_time_is_bounded` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.relative_rtc_time_is_bounded` | `relative_rtc_time_is_bounded_correspondence` | [view](3_printed_declarations/relative_rtc_time_is_bounded.md) |
| `job_receives_enough_service_1` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.job_receives_enough_service_1` | `job_receives_enough_service_1_correspondence` | [view](3_printed_declarations/job_receives_enough_service_1.md) |
| `job_receives_enough_service_2` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.job_receives_enough_service_2` | `job_receives_enough_service_2_correspondence` | [view](3_printed_declarations/job_receives_enough_service_2.md) |
| `job_receives_enough_service_3` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.job_receives_enough_service_3` | `job_receives_enough_service_3_correspondence` | [view](3_printed_declarations/job_receives_enough_service_3.md) |
| `job_is_completed_by_arrival_plus_R` | Lemma | `Prosa.Analysis.Abstract.AbstractRta.job_is_completed_by_arrival_plus_R` | `job_is_completed_by_arrival_plus_R_correspondence` | [view](3_printed_declarations/job_is_completed_by_arrival_plus_R.md) |
| `uniprocessor_response_time_bound` | Theorem | `Prosa.Analysis.Abstract.AbstractRta.uniprocessor_response_time_bound` | `uniprocessor_response_time_bound_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound.md) |

## Certificates

| Module | Role |
|---|---|
| [`AbstractRtaCorrespondence`](4_correspondence/AbstractRtaCorrespondence.v) | Correspondences for `analysis/abstract/abstract_rta.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
