# `analysis/facts/preemption/rtc_threshold/nonpreemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_rtc_threshold_is_0` | Fact | `Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.job_rtc_threshold_is_0` | `job_rtc_threshold_is_0_correspondence` | [view](3_printed_declarations/job_rtc_threshold_is_0.md) |
| `job_rtc_threshold_is_ε` | Fact | `Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.job_rtc_threshold_is_ε` | `job_rtc_threshold_is_ε_correspondence` | [view](3_printed_declarations/job_rtc_threshold_is_ε.md) |
| `fully_nonpreemptive_valid_task_run_to_completion_threshold` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold` | `fully_nonpreemptive_valid_task_run_to_completion_threshold_correspondence` | [view](3_printed_declarations/fully_nonpreemptive_valid_task_run_to_completion_threshold.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsRtcNonpreemptiveCorrespondence`](4_correspondence/FactsRtcNonpreemptiveCorrespondence.v) | Statement correspondences for `analysis/facts/preemption/rtc_threshold/nonpreemptive.v`: the extracted statements (elaborated with the source's section-local fully nonpreemptive job and … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
