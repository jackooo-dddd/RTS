# `analysis/abstract/search_space.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `are_equivalent_at_values_less_than` | Definition | `Prosa.Analysis.Abstract.SearchSpace.are_equivalent_at_values_less_than` | `ss_equivalent_correspondence` | [view](3_printed_declarations/are_equivalent_at_values_less_than.md) |
| `are_not_equivalent_at_values_less_than` | Definition | `Prosa.Analysis.Abstract.SearchSpace.are_not_equivalent_at_values_less_than` | `ss_not_equivalent_correspondence` | [view](3_printed_declarations/are_not_equivalent_at_values_less_than.md) |
| `is_in_search_space` | Definition | `Prosa.Analysis.Abstract.SearchSpace.is_in_search_space` | `ss_search_space_correspondence` | [view](3_printed_declarations/is_in_search_space.md) |
| `representative_exists` | Lemma | `Prosa.Analysis.Abstract.SearchSpace.representative_exists` | `ss_representative_statement_correspondence` | [view](3_printed_declarations/representative_exists.md) |
| `solution_for_A_exists` | Lemma | `Prosa.Analysis.Abstract.SearchSpace.solution_for_A_exists` | `ss_solution_statement_correspondence` | [view](3_printed_declarations/solution_for_A_exists.md) |
| `search_space_switch_IBF` | Lemma | `Prosa.Analysis.Abstract.SearchSpace.search_space_switch_IBF` | `ss_switch_statement_correspondence` | [view](3_printed_declarations/search_space_switch_IBF.md) |

## Certificates

| Module | Role |
|---|---|
| [`SearchSpaceBaseAdapter`](4_correspondence/SearchSpaceBaseAdapter.v) | All relations below are about actual imported constructors and operations. |
| [`SearchSpaceExactTypeGuards`](4_correspondence/SearchSpaceExactTypeGuards.v) | Proves or defines `ss_guard_add`, `ss_guard_sub_one`, `ss_target_equivalent_type_guard` and 5 more. |
| [`SearchSpaceLogicalOperations`](4_correspondence/SearchSpaceLogicalOperations.v) | Proves or defines `ss_and_correspondence`, `ss_andb_elim`, `ss_andb_intro` and 5 more. |
| [`SearchSpaceDefinitionsCorrespondence`](4_correspondence/SearchSpaceDefinitionsCorrespondence.v) | Proves or defines `ss_range_intro`, `ss_range_elim`, `ss_value_eq_correspondence` and 7 more. |
| [`SearchSpaceRepresentativeCorrespondence`](4_correspondence/SearchSpaceRepresentativeCorrespondence.v) | Proves or defines `ss_representative_conclusion_correspondence`, `ss_representative_statement_correspondence`. |
| [`SearchSpaceSolutionCorrespondence`](4_correspondence/SearchSpaceSolutionCorrespondence.v) | Proves or defines `ss_solution_conclusion_correspondence`, `ss_solution_statement_correspondence`. |
| [`SearchSpaceSwitchCorrespondence`](4_correspondence/SearchSpaceSwitchCorrespondence.v) | Proves or defines `ss_ibf_equal_below_correspondence`, `ss_switch_at_correspondence`, `ss_switch_forall_A_correspondence` and 1 more. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `SubNatTrue`, `eq` |
| Rocq primitives | — |
