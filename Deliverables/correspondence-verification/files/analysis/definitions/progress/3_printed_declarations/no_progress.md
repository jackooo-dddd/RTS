# `no_progress`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.progress.no_progress`
- Lean: `Prosa.Analysis.Definitions.Progress.no_progress`
- Certificate: `no_progress_correspondence`

## Official Rocq

```coq
no_progress :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Job -> nat -> nat -> bool

no_progress is not universe polymorphic
Arguments no_progress {Job PState} sched j (t1 t2)%nat_scope
no_progress is transparent
Expands to: Constant prosa.analysis.definitions.progress.no_progress
Declared in library prosa.analysis.definitions.progress, line 33, characters 15-26
@no_progress
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Equality.sort Job -> nat -> nat -> bool
```

Body:

```coq
no_progress =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : nat) =>
@service Job PState sched j t1 == @service Job PState sched j t2
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Job -> nat -> nat -> bool

Arguments no_progress {Job PState} sched j (t1 t2)%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Progress.no_progress : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Job → ℕ → ℕ → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.Progress.no_progress.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → ℕ → ℕ → Bool :=
fun {Job} [DecidableEq Job] {PState} sched j t1 t2 =>
  decide (Prosa.Behavior.Service.service sched j t1 = Prosa.Behavior.Service.service sched j t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Progress_no_progress
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Nat -> Nat -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Progress_no_progress@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t1 t2 : Nat) =>
Decidable_decide
  (@eq Prosa_Behavior_Job_work
     (Prosa_Behavior_Service_service Job
        inst_3 PState sched j t1)
     (Prosa_Behavior_Service_service Job
        inst_3 PState sched j t2))
  (instDecidableEqNat
     (Prosa_Behavior_Service_service Job
        inst_3 PState sched j t1)
     (Prosa_Behavior_Service_service Job
        inst_3 PState sched j t2))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Nat -> Nat -> Bool

Arguments Prosa_Analysis_Definitions_Progress_no_progress Job
  inst_3 PState 
  sched j (t1 x____at___Init_Prelude2408276647__hygCtx__hyg14)%_Nat_scope
```
