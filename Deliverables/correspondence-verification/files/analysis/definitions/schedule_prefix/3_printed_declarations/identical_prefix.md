# `identical_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.schedule_prefix.identical_prefix`
- Lean: `Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix`
- Certificate: `identical_prefix_correspondence`

## Official Rocq

```coq
identical_prefix :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> @schedule Job PState -> instant -> Prop

identical_prefix is not universe polymorphic
Arguments identical_prefix {Job PState} sched sched' horizon
identical_prefix is transparent
Expands to: Constant prosa.analysis.definitions.schedule_prefix.identical_prefix
Declared in library prosa.analysis.definitions.schedule_prefix, line 16, characters 13-29
@identical_prefix
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> @schedule Job PState -> instant -> Prop
```

Body:

```coq
identical_prefix =
fun (Job : JobType) (PState : ProcessorState Job) (sched sched' : @schedule Job PState) (horizon : instant) =>
forall t : nat, is_true (t < horizon) -> sched t = sched' t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> @schedule Job PState -> instant -> Prop

Arguments identical_prefix {Job PState} sched sched' horizon
```

## Lean

```lean
@Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prop
def Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prop :=
fun {Job} [DecidableEq Job] {PState} sched sched' horizon => ∀ t < horizon, sched t = sched' t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched
   sched' : Prosa_Behavior_Schedule_schedule Job
              inst_3 PState)
  (horizon : Prosa_Behavior_Time_instant) =>
forall t : Prosa_Behavior_Time_instant,
LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t horizon ->
@eq
  (Prosa_Behavior_Schedule_ProcessorState_State Job
     inst_3 PState)
  (sched t) (sched' t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
  inst_3 PState 
  sched sched' horizon
```
