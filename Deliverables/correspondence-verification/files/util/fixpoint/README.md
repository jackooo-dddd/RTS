# `util/fixpoint.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `find_fixpoint_from` | Fixpoint | `Prosa.Util.Fixpoint.find_fixpoint_from` | `fixpoint_from_correspondence` | [view](3_printed_declarations/find_fixpoint_from.md) |
| `find_fixpoint` | Definition | `Prosa.Util.Fixpoint.find_fixpoint` | `fixpoint_correspondence` | [view](3_printed_declarations/find_fixpoint.md) |
| `ffpf_finds_fixpoint` | Lemma | `Prosa.Util.Fixpoint.ffpf_finds_fixpoint` | `fixpoint_ffpf_statement_certificate` | [view](3_printed_declarations/ffpf_finds_fixpoint.md) |
| `ffp_finds_fixpoint` | Corollary | `Prosa.Util.Fixpoint.ffp_finds_fixpoint` | `fixpoint_ffp_statement_certificate` | [view](3_printed_declarations/ffp_finds_fixpoint.md) |
| `no_fixpoint_skipped` | Lemma | `Prosa.Util.Fixpoint.no_fixpoint_skipped` | `fixpoint_no_skipped_statement_certificate` | [view](3_printed_declarations/no_fixpoint_skipped.md) |
| `ffpf_finds_least_fixpoint` | Lemma | `Prosa.Util.Fixpoint.ffpf_finds_least_fixpoint` | `fixpoint_ffpf_least_statement_certificate` | [view](3_printed_declarations/ffpf_finds_least_fixpoint.md) |
| `ffp_finds_least_fixpoint` | Corollary | `Prosa.Util.Fixpoint.ffp_finds_least_fixpoint` | `fixpoint_ffp_least_statement_certificate` | [view](3_printed_declarations/ffp_finds_least_fixpoint.md) |
| `ffpf_finds_positive_fixpoint` | Lemma | `Prosa.Util.Fixpoint.ffpf_finds_positive_fixpoint` | `fixpoint_ffpf_positive_statement_certificate` | [view](3_printed_declarations/ffpf_finds_positive_fixpoint.md) |
| `ffp_finds_positive_fixpoint` | Lemma | `Prosa.Util.Fixpoint.ffp_finds_positive_fixpoint` | `fixpoint_ffp_positive_statement_certificate` | [view](3_printed_declarations/ffp_finds_positive_fixpoint.md) |
| `ffpf_finds_none` | Lemma | `Prosa.Util.Fixpoint.ffpf_finds_none` | `fixpoint_ffpf_none_statement_certificate` | [view](3_printed_declarations/ffpf_finds_none.md) |
| `ffp_finds_none` | Lemma | `Prosa.Util.Fixpoint.ffp_finds_none` | `fixpoint_ffp_none_statement_certificate` | [view](3_printed_declarations/ffp_finds_none.md) |
| `find_max_fixpoint_of_seq` | Definition | `Prosa.Util.Fixpoint.find_max_fixpoint_of_seq` | `fixpoint_max_of_seq_correspondence` | [view](3_printed_declarations/find_max_fixpoint_of_seq.md) |
| `fmfs_finds_fixpoint` | Lemma | `Prosa.Util.Fixpoint.fmfs_finds_fixpoint` | `fixpoint_fmfs_finds_statement_certificate` | [view](3_printed_declarations/fmfs_finds_fixpoint.md) |
| `fmfs_is_maximum` | Lemma | `Prosa.Util.Fixpoint.fmfs_is_maximum` | `fixpoint_fmfs_maximum_statement_certificate` | [view](3_printed_declarations/fmfs_is_maximum.md) |
| `find_max_fixpoint` | Definition | `Prosa.Util.Fixpoint.find_max_fixpoint` | `fixpoint_max_wrapper_correspondence` | [view](3_printed_declarations/find_max_fixpoint.md) |
| `fmf_finds_fixpoint` | Corollary | `Prosa.Util.Fixpoint.fmf_finds_fixpoint` | `fixpoint_fmf_finds_statement_certificate` | [view](3_printed_declarations/fmf_finds_fixpoint.md) |
| `fmf_is_maximum` | Corollary | `Prosa.Util.Fixpoint.fmf_is_maximum` | `fixpoint_fmf_maximum_statement_certificate` | [view](3_printed_declarations/fmf_is_maximum.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `FixpointListTrue`, `FixpointTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
