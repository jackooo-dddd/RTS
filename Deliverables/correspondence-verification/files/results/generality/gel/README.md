# `results/generality/gel.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `gel_generalizes_edf` | Remark | `Prosa.Results.Generality.Gel.gel_generalizes_edf` | `gel_generalizes_edf_correspondence` | [view](3_printed_declarations/gel_generalizes_edf.md) |
| `gel_generalizes_fifo` | Remark | `Prosa.Results.Generality.Gel.gel_generalizes_fifo` | `gel_generalizes_fifo_correspondence` | [view](3_printed_declarations/gel_generalizes_fifo.md) |
| `pp_delta` | Definition | `Prosa.Results.Generality.Gel.pp_delta` | `pp_delta_correspondence` | [view](3_printed_declarations/pp_delta.md) |
| `backlogged_job_has_lower_gel_prio` | Lemma | `Prosa.Results.Generality.Gel.backlogged_job_has_lower_gel_prio` | `backlogged_job_has_lower_gel_prio_correspondence` | [view](3_printed_declarations/backlogged_job_has_lower_gel_prio.md) |
| `gel_conditionally_generalizes_fp` | Theorem | `Prosa.Results.Generality.Gel.gel_conditionally_generalizes_fp` | `gel_conditionally_generalizes_fp_correspondence` | [view](3_printed_declarations/gel_conditionally_generalizes_fp.md) |

## Certificates

| Module | Role |
|---|---|
| [`GeneralityGelCorrespondence`](4_correspondence/GeneralityGelCorrespondence.v) | Correspondences for `results/generality/gel.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `PdTrue`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
