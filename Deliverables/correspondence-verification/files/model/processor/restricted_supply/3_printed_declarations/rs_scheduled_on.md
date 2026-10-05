# `rs_scheduled_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.restricted_supply.rs_scheduled_on`
- Lean: `Prosa.Model.Processor.RestrictedSupply.rs_scheduled_on`
- Certificate: `rs_scheduled_on_correspondence`

## Official Rocq

```coq
rs_scheduled_on : forall Job : JobType, Equality.sort Job -> @processor_state Job -> bool

rs_scheduled_on is not universe polymorphic
Arguments rs_scheduled_on Job j s
rs_scheduled_on is transparent
Expands to: Constant prosa.model.processor.restricted_supply.rs_scheduled_on
Declared in library prosa.model.processor.restricted_supply, line 38, characters 15-30
rs_scheduled_on
     : forall Job : JobType, Equality.sort Job -> @processor_state Job -> bool
```

Body:

```coq
rs_scheduled_on =
fun (Job : JobType) (j : Equality.sort Job) (s : @processor_state Job) =>
match s with
| @Active _ j' | @Unavailable _ j' => j' == j
| _ => false
end
     : forall Job : JobType, Equality.sort Job -> @processor_state Job -> bool

Arguments rs_scheduled_on Job j s
```

## Lean

```lean
@Prosa.Model.Processor.RestrictedSupply.rs_scheduled_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.RestrictedSupply.processor_state Job → Bool
def Prosa.Model.Processor.RestrictedSupply.rs_scheduled_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.RestrictedSupply.processor_state Job → Bool :=
fun {Job} [DecidableEq Job] j s =>
  match s with
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Idle => false
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Inactive => false
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Active j' => decide (j' = j)
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Unavailable j' => decide (j' = j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_RestrictedSupply_processor_state Job -> Bool
```

Body:

```coq
Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (s : Prosa_Model_Processor_RestrictedSupply_processor_state Job) =>
Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_RestrictedSupply_processor_state Job => Bool) s 
  (fun _ : Unit => Bool_false) (fun _ : Unit => Bool_false)
  (fun j' : Job =>
   Decidable_decide (@eq Job j' j)
     (inst_3 j' j))
  (fun j' : Job =>
   Decidable_decide (@eq Job j' j)
     (inst_3 j' j))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_RestrictedSupply_processor_state Job -> Bool

Arguments Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on Job
  inst_3 j s
```
