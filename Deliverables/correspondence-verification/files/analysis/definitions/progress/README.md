# `analysis/definitions/progress.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_has_progressed` | Definition | `Prosa.Analysis.Definitions.Progress.job_has_progressed` | `job_has_progressed_correspondence` | [view](3_printed_declarations/job_has_progressed.md) |
| `no_progress` | Definition | `Prosa.Analysis.Definitions.Progress.no_progress` | `no_progress_correspondence` | [view](3_printed_declarations/no_progress.md) |
| `no_progress_equiv` | Lemma | `Prosa.Analysis.Definitions.Progress.no_progress_equiv` | `no_progress_equiv_correspondence` | [view](3_printed_declarations/no_progress_equiv.md) |
| `no_progress_for` | Definition | `Prosa.Analysis.Definitions.Progress.no_progress_for` | `no_progress_for_correspondence` | [view](3_printed_declarations/no_progress_for.md) |

## Certificates

| Module | Role |
|---|---|
| [`ProgressCorrespondence`](4_correspondence/ProgressCorrespondence.v) | Correspondences for `analysis/definitions/progress.v`: for related processor states (two-sided `SvcProcessorStateRel`) and schedules, the three extracted source definitions and the compiled Lean … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
