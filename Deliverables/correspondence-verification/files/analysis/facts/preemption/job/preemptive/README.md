# `analysis/facts/preemption/job/preemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `valid_fully_preemptive_model` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Preemptive.valid_fully_preemptive_model` | `valid_fully_preemptive_model_correspondence` | [view](3_printed_declarations/valid_fully_preemptive_model.md) |
| `job_max_nps_is_0` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Preemptive.job_max_nps_is_0` | `job_max_nps_is_0_correspondence` | [view](3_printed_declarations/job_max_nps_is_0.md) |
| `job_max_nps_is_ε` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Preemptive.job_max_nps_is_ε` | `job_max_nps_is_ε_correspondence` | [view](3_printed_declarations/job_max_nps_is_ε.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPreemptiveJobCorrespondence`](4_correspondence/FactsPreemptiveJobCorrespondence.v) | Statement correspondences for `analysis/facts/preemption/job/preemptive.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
