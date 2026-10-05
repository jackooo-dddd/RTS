# `all_deadlines_met`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.schedulability.all_deadlines_met`
- Lean: `Prosa.Analysis.Definitions.Schedulability.all_deadlines_met`
- Certificate: `all_deadlines_met_correspondence`

## Official Rocq

```coq
all_deadlines_met :
forall {Job : JobType},
JobCost Job -> JobDeadline Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

all_deadlines_met is not universe polymorphic
Arguments all_deadlines_met {Job H0 H1 PState} sched
all_deadlines_met is transparent
Expands to: Constant prosa.analysis.definitions.schedulability.all_deadlines_met
Declared in library prosa.analysis.definitions.schedulability, line 124, characters 13-30
@all_deadlines_met
     : forall Job : JobType,
       JobCost Job -> JobDeadline Job -> forall PState : ProcessorState Job, @schedule Job PState -> Prop
```

Body:

```coq
all_deadlines_met =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobDeadline Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) =>
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> is_true (@job_meets_deadline Job PState sched H0 H1 j)
     : forall {Job : JobType},
       JobCost Job -> JobDeadline Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

Arguments all_deadlines_met {Job H0 H1 PState} sched
```

## Lean

```lean
@Prosa.Analysis.Definitions.Schedulability.all_deadlines_met : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Schedulability.all_deadlines_met.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobDeadline Job] {PState} sched =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Service.job_meets_deadline sched j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Schedulability_all_deadlines_met
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Schedulability_all_deadlines_met@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobDeadline Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_job_meets_deadline Job
     inst_3 PState sched
     inst_6
     inst_9 j)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Analysis_Definitions_Schedulability_all_deadlines_met Job
  inst_3
  inst_6
  inst_9 PState 
  sched
```
