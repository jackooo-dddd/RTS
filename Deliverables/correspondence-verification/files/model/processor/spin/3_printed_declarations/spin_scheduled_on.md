# `spin_scheduled_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.spin.spin_scheduled_on`
- Lean: `Prosa.Model.Processor.Spin.spin_scheduled_on`
- Certificate: `spin_scheduled_on_correspondence`

## Official Rocq

```coq
spin_scheduled_on : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> bool

spin_scheduled_on is not universe polymorphic
Arguments spin_scheduled_on Job j s _
spin_scheduled_on is transparent
Expands to: Constant prosa.model.processor.spin.spin_scheduled_on
Declared in library prosa.model.processor.spin, line 30, characters 15-32
spin_scheduled_on
     : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> bool
```

Body:

```coq
spin_scheduled_on =
fun (Job : JobType) (j : Equality.sort Job) (s : processor_state Job) =>
fun=> match s with
      | @Idle _ => false
      | @Spin _ j' | @Progress _ j' => j' == j
      end
     : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> bool

Arguments spin_scheduled_on Job j s _
```

## Lean

```lean
@Prosa.Model.Processor.Spin.spin_scheduled_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Spin.processor_state Job → Unit → Bool
def Prosa.Model.Processor.Spin.spin_scheduled_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Spin.processor_state Job → Unit → Bool :=
fun {Job} [DecidableEq Job] j s x =>
  match s with
  | Prosa.Model.Processor.Spin.processor_state.Idle => false
  | Prosa.Model.Processor.Spin.processor_state.Spin j' => decide (j' = j)
  | Prosa.Model.Processor.Spin.processor_state.Progress j' => decide (j' = j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Spin_spin_scheduled_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_Spin_processor_state Job -> Unit -> Bool
```

Body:

```coq
Prosa_Model_Processor_Spin_spin_scheduled_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (s : Prosa_Model_Processor_Spin_processor_state Job) (_ : Unit) =>
Prosa_Model_Processor_Spin_spin_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_Spin_processor_state Job => Bool) s (fun _ : Unit => Bool_false)
  (fun j' : Job =>
   Decidable_decide (@eq Job j' j) (inst_3 j' j))
  (fun j' : Job =>
   Decidable_decide (@eq Job j' j) (inst_3 j' j))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_Spin_processor_state Job -> Unit -> Bool

Arguments Prosa_Model_Processor_Spin_spin_scheduled_on Job
  inst_3 j s
  x____at___Prosa_Model_Processor_Spin415965251__hygCtx__hyg9
```
