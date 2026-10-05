# `analysis/transform/wc_trans.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `relevant_pstate` | Definition | `Prosa.Analysis.Transform.WcTrans.relevant_pstate` | `relevant_pstate_correspondence` | [view](3_printed_declarations/relevant_pstate.md) |
| `max_deadline_for_jobs_arrived_before` | Definition | `Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before` | `max_deadline_for_jobs_arrived_before_correspondence` | [view](3_printed_declarations/max_deadline_for_jobs_arrived_before.md) |
| `find_swap_candidate` | Definition | `Prosa.Analysis.Transform.WcTrans.find_swap_candidate` | `find_swap_candidate_correspondence` | [view](3_printed_declarations/find_swap_candidate.md) |
| `make_wc_at` | Definition | `Prosa.Analysis.Transform.WcTrans.make_wc_at` | `make_wc_at_correspondence` | [view](3_printed_declarations/make_wc_at.md) |
| `wc_transform_prefix` | Definition | `Prosa.Analysis.Transform.WcTrans.wc_transform_prefix` | `wc_transform_prefix_correspondence` | [view](3_printed_declarations/wc_transform_prefix.md) |
| `wc_transform` | Definition | `Prosa.Analysis.Transform.WcTrans.wc_transform` | `wc_transform_correspondence` | [view](3_printed_declarations/wc_transform.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
