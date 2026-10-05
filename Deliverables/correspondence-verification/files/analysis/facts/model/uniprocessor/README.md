# `analysis/facts/model/uniprocessor.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `scheduled_job_at_neq` | Lemma | `Prosa.Analysis.Facts.Model.Uniprocessor.scheduled_job_at_neq` | `scheduled_job_at_neq_statement_correspondence` | [view](3_printed_declarations/scheduled_job_at_neq.md) |

## Certificates

| Module | Role |
|---|---|
| [`UniPlatformPropertiesCorrespondence`](4_correspondence/UniPlatformPropertiesCorrespondence.v) | The processor-state relation is the previously certified, two-sided observational representation relation, recompiled against this exact imported artifact. |
| [`UniprocessorCorrespondence`](4_correspondence/UniprocessorCorrespondence.v) | Statement correspondence for `scheduled_job_at_neq`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SchSourceTrue`, `SchTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
