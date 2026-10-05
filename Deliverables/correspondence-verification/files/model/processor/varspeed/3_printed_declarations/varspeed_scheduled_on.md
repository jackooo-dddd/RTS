# `varspeed_scheduled_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.varspeed.varspeed_scheduled_on`
- Lean: `Prosa.Model.Processor.Varspeed.varspeed_scheduled_on`
- Certificate: `vs_scheduled_on_correspondence`

## Official Rocq

```coq
varspeed_scheduled_on : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> bool

varspeed_scheduled_on is not universe polymorphic
Arguments varspeed_scheduled_on Job j s _
varspeed_scheduled_on is transparent
Expands to: Constant prosa.model.processor.varspeed.varspeed_scheduled_on
Declared in library prosa.model.processor.varspeed, line 32, characters 15-36
varspeed_scheduled_on
     : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> bool
```

Body:

```coq
varspeed_scheduled_on =
fun (Job : JobType) (j : Equality.sort Job) (s : processor_state Job) =>
fun=> match s with
      | @Idle _ _ => false
      | @Progress _ j' _ => j' == j
      end
     : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> bool

Arguments varspeed_scheduled_on Job j s _
```

## Lean

```lean
@Prosa.Model.Processor.Varspeed.varspeed_scheduled_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Varspeed.processor_state Job → Unit → Bool
def Prosa.Model.Processor.Varspeed.varspeed_scheduled_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Varspeed.processor_state Job → Unit → Bool :=
fun {Job} [DecidableEq Job] j s x =>
  match s with
  | Prosa.Model.Processor.Varspeed.processor_state.Idle speed => false
  | Prosa.Model.Processor.Varspeed.processor_state.Progress j' speed => decide (j' = j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Varspeed_varspeed_scheduled_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_Varspeed_processor_state Job -> Unit -> Bool
```

Body:

```coq
Prosa_Model_Processor_Varspeed_varspeed_scheduled_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (s : Prosa_Model_Processor_Varspeed_processor_state Job) (_ : Unit) =>
Prosa_Model_Processor_Varspeed_varspeed_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_Varspeed_processor_state Job => Bool) s (fun _ : Nat => Bool_false)
  (fun (j' : Job) (_ : Nat) =>
   Decidable_decide (@eq Job j' j) (inst_3 j' j))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_Varspeed_processor_state Job -> Unit -> Bool

Arguments Prosa_Model_Processor_Varspeed_varspeed_scheduled_on Job
  inst_3 j s
  x____at___Prosa_Model_Processor_Varspeed3198291132__hygCtx__hyg9
```
