# `jobs_must_be_ready_to_execute`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.ready.jobs_must_be_ready_to_execute`
- Lean: `Prosa.Behavior.Ready.jobs_must_be_ready_to_execute`
- Certificate: ``

## Official Rocq

```coq
jobs_must_be_ready_to_execute :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job},
@schedule Job PState -> forall {H0 : JobCost Job}, @JobReady Job PState H0 H -> Prop

jobs_must_be_ready_to_execute is not universe polymorphic
Arguments jobs_must_be_ready_to_execute {Job H PState} sched {H0 JobReady0}
jobs_must_be_ready_to_execute is transparent
Expands to: Constant prosa.behavior.ready.jobs_must_be_ready_to_execute
Declared in library prosa.behavior.ready, line 63, characters 13-42
@jobs_must_be_ready_to_execute
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job),
       @schedule Job PState -> forall H0 : JobCost Job, @JobReady Job PState H0 H -> Prop
```

Body:

```coq
jobs_must_be_ready_to_execute =
fun (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (H0 : JobCost Job) (JobReady0 : @JobReady Job PState H0 H) =>
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> is_true (@job_ready Job PState H0 H JobReady0 sched j t)
     : forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job},
       @schedule Job PState -> forall {H0 : JobCost Job}, @JobReady Job PState H0 H -> Prop

Arguments jobs_must_be_ready_to_execute {Job H PState} sched {H0 JobReady0}
```

## Lean

```lean
@Prosa.Behavior.Ready.jobs_must_be_ready_to_execute : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Schedule.schedule PState →
          [inst_2 : Prosa.Behavior.Job.JobCost Job] → [Prosa.Behavior.Ready.JobReady Job PState] → Prop
def Prosa.Behavior.Ready.jobs_must_be_ready_to_execute.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Schedule.schedule PState →
          [inst_2 : Prosa.Behavior.Job.JobCost Job] → [Prosa.Behavior.Ready.JobReady Job PState] → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] {PState} sched [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Behavior.Ready.JobReady Job PState] =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Ready.job_ready sched j t = true
```

## Lean, imported into Rocq

```coq
ImportedReady.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (inst_6 : ImportedReady.Prosa_Behavior_Job_JobArrival
                                                                        Job
                                                                        inst_3)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall
         inst_13 : ImportedReady.Prosa_Behavior_Job_JobCost
                                                                        Job
                                                                        inst_3,
       ImportedReady.Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_13
         inst_6 ->
       SProp
```

Body:

```coq
ImportedReady.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedReady.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedReady.DecidableEq Job)
  (inst_6 : 
   ImportedReady.Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedReady.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (inst_13 : 
   ImportedReady.Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_16 : 
   ImportedReady.Prosa_Behavior_Ready_JobReady Job
     inst_3
     PState
     inst_13
     inst_6) =>
forall (j : Job) (t : ImportedReady.Prosa_Behavior_Time_instant),
@eq ImportedReady.Bool
  (ImportedReady.Prosa_Behavior_Service_scheduled_at Job
     inst_3
     PState sched j t)
  ImportedReady.Bool_true ->
@eq ImportedReady.Bool
  (ImportedReady.Prosa_Behavior_Ready_JobReady_job_ready Job
     inst_3
     PState
     inst_13
     inst_6
     inst_16
     sched j t)
  ImportedReady.Bool_true
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (inst_6 : ImportedReady.Prosa_Behavior_Job_JobArrival
                                                                        Job
                                                                        inst_3)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall
         inst_13 : ImportedReady.Prosa_Behavior_Job_JobCost
                                                                        Job
                                                                        inst_3,
       ImportedReady.Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_13
         inst_6 ->
       SProp

Arguments ImportedReady.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job
  inst_3
  inst_6 PState sched
  inst_13
  inst_16
```
