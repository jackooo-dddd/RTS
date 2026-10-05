# `completed_jobs_dont_execute`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.ready.completed_jobs_dont_execute`
- Lean: `Prosa.Behavior.Ready.completed_jobs_dont_execute`
- Certificate: ``

## Official Rocq

```coq
completed_jobs_dont_execute :
forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> JobCost Job -> Prop

completed_jobs_dont_execute is not universe polymorphic
Arguments completed_jobs_dont_execute {Job PState} sched {H0}
completed_jobs_dont_execute is transparent
Expands to: Constant prosa.behavior.ready.completed_jobs_dont_execute
Declared in library prosa.behavior.ready, line 67, characters 13-40
@completed_jobs_dont_execute
     : forall (Job : JobType) (PState : ProcessorState Job), @schedule Job PState -> JobCost Job -> Prop
```

Body:

```coq
completed_jobs_dont_execute =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (H0 : JobCost Job) =>
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> is_true (@service Job PState sched j t < @job_cost Job H0 j)
     : forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> JobCost Job -> Prop

Arguments completed_jobs_dont_execute {Job PState} sched {H0}
```

## Lean

```lean
@Prosa.Behavior.Ready.completed_jobs_dont_execute : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → [Prosa.Behavior.Job.JobCost Job] → Prop
def Prosa.Behavior.Ready.completed_jobs_dont_execute.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → [Prosa.Behavior.Job.JobCost Job] → Prop :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Behavior.Job.JobCost Job] =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.scheduled_at sched j t = true →
      Prosa.Behavior.Service.service sched j t < Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
ImportedReady.Prosa_Behavior_Ready_completed_jobs_dont_execute
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedReady.Prosa_Behavior_Job_JobCost Job inst_3 ->
       SProp
```

Body:

```coq
ImportedReady.Prosa_Behavior_Ready_completed_jobs_dont_execute@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedReady.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedReady.DecidableEq Job)
  (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedReady.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (inst_10 : 
   ImportedReady.Prosa_Behavior_Job_JobCost Job
     inst_3) =>
forall (j : Job) (t : ImportedReady.Prosa_Behavior_Time_instant),
@eq ImportedReady.Bool
  (ImportedReady.Prosa_Behavior_Service_scheduled_at Job
     inst_3
     PState sched j t)
  ImportedReady.Bool_true ->
ImportedReady.LT_lt_inst1 ImportedReady.Prosa_Behavior_Job_work ImportedReady.instLTNat
  (ImportedReady.Prosa_Behavior_Service_service Job
     inst_3
     PState sched j t)
  (ImportedReady.Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_10 j)
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedReady.Prosa_Behavior_Job_JobCost Job inst_3 ->
       SProp

Arguments ImportedReady.Prosa_Behavior_Ready_completed_jobs_dont_execute Job
  inst_3 PState sched
  inst_13
```
