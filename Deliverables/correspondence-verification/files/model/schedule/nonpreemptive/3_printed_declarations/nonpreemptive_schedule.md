# `nonpreemptive_schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.nonpreemptive.nonpreemptive_schedule`
- Lean: `Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule`
- Certificate: `nonpreemptive_schedule_correspondence`

## Official Rocq

```coq
nonpreemptive_schedule :
forall {Job : JobType}, JobCost Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

nonpreemptive_schedule is not universe polymorphic
Arguments nonpreemptive_schedule {Job H PState} sched
nonpreemptive_schedule is transparent
Expands to: Constant prosa.model.schedule.nonpreemptive.nonpreemptive_schedule
Declared in library prosa.model.schedule.nonpreemptive, line 20, characters 13-35
@nonpreemptive_schedule
     : forall Job : JobType, JobCost Job -> forall PState : ProcessorState Job, @schedule Job PState -> Prop
```

Body:

```coq
nonpreemptive_schedule =
fun (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState) =>
forall (j : Equality.sort Job) (t t' : instant),
is_true (t <= t') ->
is_true (@scheduled_at Job PState sched j t) ->
is_true (~~ @completed_by Job PState sched H j t') -> is_true (@scheduled_at Job PState sched j t')
     : forall {Job : JobType},
       JobCost Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

Arguments nonpreemptive_schedule {Job H PState} sched
```

## Lean

```lean
@Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] {PState} sched =>
  ∀ (j : Job) (t t' : Prosa.Behavior.Time.instant),
    t ≤ t' →
      Prosa.Behavior.Service.scheduled_at sched j t = true →
        (!Prosa.Behavior.Service.completed_by sched j t') = true → Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                               inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (j : Job) (t t' : Prosa_Behavior_Time_instant),
LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t' ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j t)
  Bool_true ->
@eq Bool
  (Bool_not
     (Prosa_Behavior_Service_completed_by Job
        inst_3 PState sched
        inst_6 j t'))
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j t')
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule Job
  inst_3
  inst_6 PState 
  sched
```
