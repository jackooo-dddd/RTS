# `overheads_service_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overheads.overheads_service_on`
- Lean: `Prosa.Model.Processor.Overheads.overheads_service_on`
- Certificate: `ovh_service_on_correspondence`

## Official Rocq

```coq
overheads_service_on : forall Job : JobType, Equality.sort Job -> proc_state Job -> unit -> work

overheads_service_on is not universe polymorphic
Arguments overheads_service_on Job j s _
overheads_service_on is transparent
Expands to: Constant prosa.model.processor.overheads.overheads_service_on
Declared in library prosa.model.processor.overheads, line 64, characters 15-35
overheads_service_on
     : forall Job : JobType, Equality.sort Job -> proc_state Job -> unit -> work
```

Body:

```coq
overheads_service_on =
fun (Job : JobType) (j : Equality.sort Job) (s : proc_state Job) =>
fun=> match s with
      | @Progress _ j' => if j' == j then 1 else 0
      | _ => 0
      end
     : forall Job : JobType, Equality.sort Job -> proc_state Job -> unit -> work

Arguments overheads_service_on Job j s _
```

## Lean

```lean
@Prosa.Model.Processor.Overheads.overheads_service_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Overheads.proc_state Job → Unit → Prosa.Behavior.Job.work
def Prosa.Model.Processor.Overheads.overheads_service_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Overheads.proc_state Job → Unit → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] j s x =>
  Prosa.Model.Processor.Overheads.proc_state.casesOn s Nat.zero (fun x x_1 => Nat.zero) (fun x => Nat.zero)
    (fun x => Nat.zero) fun j' => if decide (j' = j) = true then Nat.zero.succ else Nat.zero
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_overheads_service_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_Overheads_proc_state Job -> Unit -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_Overheads_overheads_service_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (s : Prosa_Model_Processor_Overheads_proc_state Job) (_ : Unit) =>
Prosa_Model_Processor_Overheads_proc_state_casesOn Job
  (fun _ : Prosa_Model_Processor_Overheads_proc_state Job => Prosa_Behavior_Job_work) s 0
  (fun _ _ : Option Job => 0) (fun _ : Option Job => 0) (fun _ : Job => 0)
  (fun j' : Job =>
   ite Prosa_Behavior_Job_work
     (@eq Bool
        (Decidable_decide (@eq Job j' j)
           (inst_3 j' j))
        Bool_true)
     (instDecidableEqBool
        (Decidable_decide (@eq Job j' j)
           (inst_3 j' j))
        Bool_true)
     1 0)
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_Overheads_proc_state Job -> Unit -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_Overheads_overheads_service_on Job
  inst_3 j s
  x____at___Prosa_Model_Processor_Overheads4011597234__hygCtx__hyg8
```
