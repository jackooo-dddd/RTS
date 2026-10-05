# `overheads_scheduled_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overheads.overheads_scheduled_on`
- Lean: `Prosa.Model.Processor.Overheads.overheads_scheduled_on`
- Certificate: `ovh_scheduled_on_correspondence`

## Official Rocq

```coq
overheads_scheduled_on : forall Job : JobType, Equality.sort Job -> proc_state Job -> unit -> bool

overheads_scheduled_on is not universe polymorphic
Arguments overheads_scheduled_on Job j s _
overheads_scheduled_on is transparent
Expands to: Constant prosa.model.processor.overheads.overheads_scheduled_on
Declared in library prosa.model.processor.overheads, line 40, characters 15-37
overheads_scheduled_on
     : forall Job : JobType, Equality.sort Job -> proc_state Job -> unit -> bool
```

Body:

```coq
overheads_scheduled_on =
fun (Job : JobType) (j : Equality.sort Job) (s : proc_state Job) =>
fun=> match s with
      | @ContextSwitch _ _ (@Some _ j') | @Dispatch _ (@Some _ j') | @CacheRelatedPreemptionDelay _ j' |
        @Progress _ j' => j == j'
      | _ => false
      end
     : forall Job : JobType, Equality.sort Job -> proc_state Job -> unit -> bool

Arguments overheads_scheduled_on Job j s _
```

## Lean

```lean
@Prosa.Model.Processor.Overheads.overheads_scheduled_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Overheads.proc_state Job → Unit → Bool
def Prosa.Model.Processor.Overheads.overheads_scheduled_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Overheads.proc_state Job → Unit → Bool :=
fun {Job} [DecidableEq Job] j s x =>
  match s with
  | Prosa.Model.Processor.Overheads.proc_state.Idle => false
  | Prosa.Model.Processor.Overheads.proc_state.ContextSwitch j1 none => false
  | Prosa.Model.Processor.Overheads.proc_state.ContextSwitch j1 (some j') => decide (j = j')
  | Prosa.Model.Processor.Overheads.proc_state.Dispatch none => false
  | Prosa.Model.Processor.Overheads.proc_state.Dispatch (some j') => decide (j = j')
  | Prosa.Model.Processor.Overheads.proc_state.CacheRelatedPreemptionDelay j' => decide (j = j')
  | Prosa.Model.Processor.Overheads.proc_state.Progress j' => decide (j = j')
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_overheads_scheduled_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_Overheads_proc_state Job -> Unit -> Bool
```

Body:

```coq
Prosa_Model_Processor_Overheads_overheads_scheduled_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (s : Prosa_Model_Processor_Overheads_proc_state Job) (_ : Unit) =>
Prosa_Model_Processor_Overheads_overheads_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_Overheads_proc_state Job => Bool) s (fun _ : Unit => Bool_false)
  (fun _ : Option Job => Bool_false)
  (fun (_ : Option Job) (j' : Job) =>
   Decidable_decide (@eq Job j j') (inst_3 j j'))
  (fun _ : Unit => Bool_false)
  (fun j' : Job =>
   Decidable_decide (@eq Job j j') (inst_3 j j'))
  (fun j' : Job =>
   Decidable_decide (@eq Job j j') (inst_3 j j'))
  (fun j' : Job =>
   Decidable_decide (@eq Job j j') (inst_3 j j'))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Job -> Prosa_Model_Processor_Overheads_proc_state Job -> Unit -> Bool

Arguments Prosa_Model_Processor_Overheads_overheads_scheduled_on Job
  inst_3 j s
  x____at___Prosa_Model_Processor_Overheads215704638__hygCtx__hyg9
```
