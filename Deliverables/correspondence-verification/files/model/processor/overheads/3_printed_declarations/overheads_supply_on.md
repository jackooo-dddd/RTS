# `overheads_supply_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overheads.overheads_supply_on`
- Lean: `Prosa.Model.Processor.Overheads.overheads_supply_on`
- Certificate: `ovh_supply_on_correspondence`

## Official Rocq

```coq
overheads_supply_on : forall Job : JobType, proc_state Job -> unit -> work

overheads_supply_on is not universe polymorphic
Arguments overheads_supply_on Job s _
overheads_supply_on is transparent
Expands to: Constant prosa.model.processor.overheads.overheads_supply_on
Declared in library prosa.model.processor.overheads, line 55, characters 15-34
overheads_supply_on
     : forall Job : JobType, proc_state Job -> unit -> work
```

Body:

```coq
overheads_supply_on =
fun (Job : JobType) (s : proc_state Job) => fun=> match s with
                                                  | @Idle _ | @Progress _ _ => 1
                                                  | _ => 0
                                                  end
     : forall Job : JobType, proc_state Job -> unit -> work

Arguments overheads_supply_on Job s _
```

## Lean

```lean
@Prosa.Model.Processor.Overheads.overheads_supply_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.Overheads.proc_state Job → Unit → Prosa.Behavior.Job.work
def Prosa.Model.Processor.Overheads.overheads_supply_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.Overheads.proc_state Job → Unit → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] s x =>
  Prosa.Model.Processor.Overheads.proc_state.casesOn s Nat.zero.succ (fun x x_1 => Nat.zero) (fun x => Nat.zero)
    (fun x => Nat.zero) fun x => Nat.zero.succ
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_overheads_supply_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Prosa_Model_Processor_Overheads_proc_state Job -> Unit -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_Overheads_overheads_supply_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType) (_ : DecidableEq Job)
  (s : Prosa_Model_Processor_Overheads_proc_state Job) (_ : Unit) =>
Prosa_Model_Processor_Overheads_proc_state_casesOn Job
  (fun _ : Prosa_Model_Processor_Overheads_proc_state Job => Prosa_Behavior_Job_work) s 1
  (fun _ _ : Option Job => 0) (fun _ : Option Job => 0) (fun _ : Job => 0) (fun _ : Job => 1)
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Prosa_Model_Processor_Overheads_proc_state Job -> Unit -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_Overheads_overheads_supply_on Job
  inst_3 s
  x____at___Prosa_Model_Processor_Overheads4011597234__hygCtx__hyg8
```
