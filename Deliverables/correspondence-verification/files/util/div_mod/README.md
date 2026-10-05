# `util/div_mod.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `eqdivn_leqmodn` | Lemma | `Prosa.Util.Div_mod.eqdivn_leqmodn` | `eqdivn_leqmodn_statement_certificate` | [view](3_printed_declarations/eqdivn_leqmodn.md) |
| `ltdivn_dvdn` | Lemma | `Prosa.Util.Div_mod.ltdivn_dvdn` | `ltdivn_dvdn_statement_certificate` | [view](3_printed_declarations/ltdivn_dvdn.md) |
| `addn1_modn_commute` | Lemma | `Prosa.Util.Div_mod.addn1_modn_commute` | `addn1_modn_commute_statement_certificate` | [view](3_printed_declarations/addn1_modn_commute.md) |
| `addmod_le_mod` | Lemma | `Prosa.Util.Div_mod.addmod_le_mod` | `addmod_le_mod_statement_certificate` | [view](3_printed_declarations/addmod_le_mod.md) |
| `divn_leq` | Lemma | `Prosa.Util.Div_mod.divn_leq` | `divn_leq_statement_certificate` | [view](3_printed_declarations/divn_leq.md) |
| `div_floor` | Definition | `Prosa.Util.Div_mod.div_floor` | `div_floor_definition_certificate` | [view](3_printed_declarations/div_floor.md) |
| `div_ceil` | Definition | `Prosa.Util.Div_mod.div_ceil` | `div_ceil_definition_certificate` | [view](3_printed_declarations/div_ceil.md) |
| `div_ceil0` | Lemma | `Prosa.Util.Div_mod.div_ceil0` | `div_ceil0_statement_certificate` | [view](3_printed_declarations/div_ceil0.md) |
| `div_ceil_gt0` | Lemma | `Prosa.Util.Div_mod.div_ceil_gt0` | `div_ceil_gt0_statement_certificate` | [view](3_printed_declarations/div_ceil_gt0.md) |
| `div_ceil_monotone1` | Lemma | `Prosa.Util.Div_mod.div_ceil_monotone1` | `div_ceil_monotone1_statement_certificate` | [view](3_printed_declarations/div_ceil_monotone1.md) |
| `leq_div_ceil_add1` | Lemma | `Prosa.Util.Div_mod.leq_div_ceil_add1` | `leq_div_ceil_add1_statement_certificate` | [view](3_printed_declarations/leq_div_ceil_add1.md) |
| `div_ceil_subadditive` | Lemma | `Prosa.Util.Div_mod.div_ceil_subadditive` | `div_ceil_subadditive_statement_certificate` | [view](3_printed_declarations/div_ceil_subadditive.md) |
| `div_ceil_multiple` | Lemma | `Prosa.Util.Div_mod.div_ceil_multiple` | `div_ceil_multiple_statement_certificate` | [view](3_printed_declarations/div_ceil_multiple.md) |
| `div_floor_add_g` | Lemma | `Prosa.Util.Div_mod.div_floor_add_g` | `div_floor_add_g_statement_certificate` | [view](3_printed_declarations/div_floor_add_g.md) |
| `mod_elim` | Lemma | `Prosa.Util.Div_mod.mod_elim` | `mod_elim_statement_certificate` | [view](3_printed_declarations/mod_elim.md) |

## Certificates

| Module | Role |
|---|---|
| [`DivModCertificate`](4_correspondence/DivModCertificate.v) | Actual imported target statements, specialized along the canonical `nat <-> Lean.Nat` representation map. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
