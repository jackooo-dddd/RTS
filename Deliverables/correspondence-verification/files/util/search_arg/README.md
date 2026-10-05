# `util/search_arg.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `earliest_pred_element_exists_case` | Lemma | `Prosa.Util.SearchArg.earliest_pred_element_exists_case` | `earliest_pred_element_exists_case_statement_certificate` | [view](3_printed_declarations/earliest_pred_element_exists_case.md) |
| `search_arg` | Fixpoint | `Prosa.Util.SearchArg.search_arg` | `search_arg_definition_certificate` | [view](3_printed_declarations/search_arg.md) |
| `search_arg_none` | Lemma | `Prosa.Util.SearchArg.search_arg_none` | `search_arg_none_statement_certificate` | [view](3_printed_declarations/search_arg_none.md) |
| `search_arg_not_none` | Lemma | `Prosa.Util.SearchArg.search_arg_not_none` | `search_arg_not_none_statement_certificate` | [view](3_printed_declarations/search_arg_not_none.md) |
| `search_arg_pred` | Lemma | `Prosa.Util.SearchArg.search_arg_pred` | `search_arg_pred_statement_certificate` | [view](3_printed_declarations/search_arg_pred.md) |
| `search_arg_in_range` | Lemma | `Prosa.Util.SearchArg.search_arg_in_range` | `search_arg_in_range_statement_certificate` | [view](3_printed_declarations/search_arg_in_range.md) |
| `search_arg_extremum` | Lemma | `Prosa.Util.SearchArg.search_arg_extremum` | `search_arg_extremum_statement_certificate` | [view](3_printed_declarations/search_arg_extremum.md) |
| `prop_on_ex_minn` | Lemma | `Prosa.Util.SearchArg.prop_on_ex_minn` | `prop_on_ex_minn_statement_certificate` | [view](3_printed_declarations/prop_on_ex_minn.md) |

## Certificates

| Module | Role |
|---|---|
| [`SearchArgDefinitionCertificate`](4_correspondence/SearchArgDefinitionCertificate.v) | Proves or defines `sa_bool_to_imported`, `sa_option_to_imported`, `sa_target_f` and 16 more. |
| [`SearchArgStatementCertificate`](4_correspondence/SearchArgStatementCertificate.v) | Logical and representation adapters for theorem statements surrounding the already-certified recursive `search_arg` computation. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
