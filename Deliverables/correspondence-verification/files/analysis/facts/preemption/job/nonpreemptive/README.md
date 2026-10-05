# `analysis/facts/preemption/job/nonpreemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `valid_fully_nonpreemptive_model` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.valid_fully_nonpreemptive_model` | `valid_fully_nonpreemptive_model_correspondence` | [view](3_printed_declarations/valid_fully_nonpreemptive_model.md) |
| `job_max_nps_is_job_cost` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.job_max_nps_is_job_cost` | `job_max_nps_is_job_cost_correspondence` | [view](3_printed_declarations/job_max_nps_is_job_cost.md) |
| `job_last_nps_is_job_cost` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.job_last_nps_is_job_cost` | `job_last_nps_is_job_cost_correspondence` | [view](3_printed_declarations/job_last_nps_is_job_cost.md) |
| `no_preemptions_equiv_nonpreemptive` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.no_preemptions_equiv_nonpreemptive` | `no_preemptions_equiv_nonpreemptive_correspondence` | [view](3_printed_declarations/no_preemptions_equiv_nonpreemptive.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsNonpreemptiveJobCorrespondence`](4_correspondence/FactsNonpreemptiveJobCorrespondence.v) | Statement correspondences for `analysis/facts/preemption/job/nonpreemptive.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
