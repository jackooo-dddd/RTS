# `varspeed_supply_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.varspeed.varspeed_supply_on`
- Lean: `Prosa.Model.Processor.Varspeed.varspeed_supply_on`
- Certificate: `vs_supply_on_correspondence`

## Official Rocq

```coq
varspeed_supply_on : forall Job : JobType, processor_state Job -> unit -> work

varspeed_supply_on is not universe polymorphic
Arguments varspeed_supply_on Job s _
varspeed_supply_on is transparent
Expands to: Constant prosa.model.processor.varspeed.varspeed_supply_on
Declared in library prosa.model.processor.varspeed, line 42, characters 15-33
varspeed_supply_on
     : forall Job : JobType, processor_state Job -> unit -> work
```

Body:

```coq
varspeed_supply_on =
fun (Job : JobType) (s : processor_state Job) => fun=> match s with
                                                       | @Idle _ k | @Progress _ _ k => k
                                                       end
     : forall Job : JobType, processor_state Job -> unit -> work

Arguments varspeed_supply_on Job s _
```

## Lean

```lean
@Prosa.Model.Processor.Varspeed.varspeed_supply_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.Varspeed.processor_state Job → Unit → Prosa.Behavior.Job.work
def Prosa.Model.Processor.Varspeed.varspeed_supply_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.Varspeed.processor_state Job → Unit → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] s x =>
  match s with
  | Prosa.Model.Processor.Varspeed.processor_state.Idle speed => speed
  | Prosa.Model.Processor.Varspeed.processor_state.Progress j speed => speed
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Varspeed_varspeed_supply_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_Varspeed_processor_state Job -> Unit -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_Varspeed_varspeed_supply_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType) (_ : DecidableEq Job)
  (s : Prosa_Model_Processor_Varspeed_processor_state Job) (_ : Unit) =>
Prosa_Model_Processor_Varspeed_varspeed_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_Varspeed_processor_state Job => Prosa_Behavior_Job_work) s
  (fun speed : Nat => speed) (fun (_ : Job) (speed : Nat) => speed)
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_Varspeed_processor_state Job -> Unit -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_Varspeed_varspeed_supply_on Job
  inst_3 s
  x____at___Prosa_Model_Processor_Varspeed3103343038__hygCtx__hyg8
```
