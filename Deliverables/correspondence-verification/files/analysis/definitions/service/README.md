# `analysis/definitions/service.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `served_jobs_at` | Definition | `Prosa.Analysis.Definitions.Service.served_jobs_at` | `served_jobs_at_correspondence` | [view](3_printed_declarations/served_jobs_at.md) |
| `served_job_at` | Definition | `Prosa.Analysis.Definitions.Service.served_job_at` | `served_job_at_correspondence` | [view](3_printed_declarations/served_job_at.md) |

## Certificates

| Module | Role |
|---|---|
| [`AnalysisServiceCorrespondence`](4_correspondence/AnalysisServiceCorrespondence.v) | The option bridge is value-level and reusable for any imported List/Option with the same constructors and head computation. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
