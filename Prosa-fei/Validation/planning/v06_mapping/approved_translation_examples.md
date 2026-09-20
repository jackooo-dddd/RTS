# Approved Translation Examples

These examples illustrate reusable techniques. They do not make the current
Lean tree authoritative, and they do not count toward the future v0.6
translation coverage.

| Category | Source and declaration | Current Lean declaration | Why useful | Semantic-validation status |
|---|---|---|---|---|
| simple definition | v0.6 `behavior/time.v`: `instant` | `Prosa.Behavior.Time.instant` | direct natural-number representation | `CERTIFIED` |
| eqType-related class | v0.6 `behavior/job.v`: `JobArrival` | `Prosa.Behavior.Job.JobArrival` | two-sided constructor/projection correspondence, while equality evidence remains explicit | `CERTIFIED` |
| representation reformulation | v0.6 `behavior/job.v`: `JobType` | `Prosa.Behavior.Job.JobType` | demonstrates why bare `Type` must be paired with `DecidableEq` | `REPRESENTATION_REFERENCE_ONLY` |
| recursive definition | v0.6 `util/list.v`: `rem_all` | `Prosa.Util.List.rem_all` | actual-artifact recursive `List`/`seq` correspondence | `CERTIFIED` |
| finite sum / bigop | v0.6 `util/sum.v`: `big_nat_eq0` | `Prosa.Util.Sum.big_nat_eq0` | reusable MathComp interval sum ↔ `Finset.Ico.sum` bridge | `CERTIFIED` (with audited Prop/SProp foundation for theorem statement) |
| inductive | v0.6 `model/processor/spin.v`: `processor_state` | `Prosa.Model.Processor.Spin.processor_state` | constructor-complete custom-inductive relation | `CERTIFIED` |
| Boolean finite existential | v0.6 `behavior/schedule.v`: `scheduled_in` | `Prosa.Behavior.Schedule.ProcessorState.scheduled_in` | finite-core existential bridge; reusable only after adapting the containing class | `REPRESENTATION_REFERENCE_ONLY` |
| evolved abstraction | v0.6 `behavior/schedule.v`: `ProcessorState` | `Prosa.Behavior.Schedule.ProcessorState` | negative example: v0.4 class shape omits v0.6 per-core operations/laws | `UNVALIDATED`; adaptation required |
| sequence function | v0.6 `behavior/arrival_sequence.v`: `arrival_sequence` | `Prosa.Behavior.Arrival_sequence.arrival_sequence` | pointwise `seq` ↔ `List` relation | `UNVALIDATED` as a closed declaration; existing result is parametric |

“Certified” here refers only to the cited existing semantic-validation result
against an actual compiled artifact. It does not certify untouched downstream
declarations or authorize copying v0.4 code without applying the migration
table and representation policy.
