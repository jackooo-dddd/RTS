# `no_progress_for`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.progress.no_progress_for`
- Lean: `Prosa.Analysis.Definitions.Progress.no_progress_for`
- Certificate: `no_progress_for_correspondence`

## Official Rocq

```coq
no_progress_for :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Job -> instant -> duration -> bool

no_progress_for is not universe polymorphic
Arguments no_progress_for {Job PState} sched j t delta
no_progress_for is transparent
Expands to: Constant prosa.analysis.definitions.progress.no_progress_for
Declared in library prosa.analysis.definitions.progress, line 60, characters 13-28
@no_progress_for
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Equality.sort Job -> instant -> duration -> bool
```

Body:

```coq
no_progress_for =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant) (delta : duration) =>
@no_progress Job PState sched j (t - delta) t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Job -> instant -> duration -> bool

Arguments no_progress_for {Job PState} sched j t delta
```

## Lean

```lean
@Prosa.Analysis.Definitions.Progress.no_progress_for : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.Progress.no_progress_for.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.duration → Bool :=
fun {Job} [DecidableEq Job] {PState} sched j t delta =>
  Prosa.Analysis.Definitions.Progress.no_progress sched j (t - delta) t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Progress_no_progress_for
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Progress_no_progress_for@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) (delta : Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_Progress_no_progress Job
  inst_3 PState sched j
  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
     (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t delta)
  t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Analysis_Definitions_Progress_no_progress_for Job
  inst_3 PState 
  sched j t delta
```
