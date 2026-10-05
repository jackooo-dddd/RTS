# `analysis/facts/model/task_cost.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_cost_positive_implies_task_cost_positive` | Lemma | `Prosa.Analysis.Facts.Model.TaskCost.job_cost_positive_implies_task_cost_positive` | `tc_positive_statement_correspondence` | [view](3_printed_declarations/job_cost_positive_implies_task_cost_positive.md) |
| `sum_job_costs_bounded` | Lemma | `Prosa.Analysis.Facts.Model.TaskCost.sum_job_costs_bounded` | `tc_sum_statement_correspondence` | [view](3_printed_declarations/sum_job_costs_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`TaskCostBaseAdapter`](4_correspondence/TaskCostBaseAdapter.v) | Artifact-local instantiation of the accepted Bool/List adapter template: IdealUniExceedFactsBaseAdapter.v, SHA-256 93b82dfed76a98760b1fae5c9f73953f251141ee7350ac256f3360289f76bb7a. |
| [`TaskCostExactTypeGuards`](4_correspondence/TaskCostExactTypeGuards.v) | Independently stated exact imported theorem interfaces. |
| [`TaskCostLogicalOperations`](4_correspondence/TaskCostLogicalOperations.v) | Proves or defines `tc_imp_correspondence`, `tc_forall_identity_correspondence`. |
| [`TaskCostClasses`](4_correspondence/TaskCostClasses.v) | The three class parameters of this source file are related inputs. |
| [`TaskCostListOperations`](4_correspondence/TaskCostListOperations.v) | Artifact-local instantiation of the accepted Schedule finite-fold pattern. |
| [`TaskCostOperations`](4_correspondence/TaskCostOperations.v) | Reused Nat/Bool/equality patterns instantiated for this actual import. |
| [`TaskCostPositiveCorrespondence`](4_correspondence/TaskCostPositiveCorrespondence.v) | Fixed related-input instance of the full positive-cost theorem statement. |
| [`TaskCostSumCorrespondence`](4_correspondence/TaskCostSumCorrespondence.v) | The list input relation preserves order and multiplicity. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq_inst1`, `SubNatTrue`, `TcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
