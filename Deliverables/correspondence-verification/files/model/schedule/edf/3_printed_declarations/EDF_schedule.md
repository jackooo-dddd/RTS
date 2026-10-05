# `EDF_schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.edf.EDF_schedule`
- Lean: `Prosa.Model.Schedule.Edf.EDF_schedule`
- Certificate: `EDF_schedule_correspondence`

## Official Rocq

```coq
EDF_schedule :
forall {Job : JobType},
JobDeadline Job -> JobArrival Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

EDF_schedule is not universe polymorphic
Arguments EDF_schedule {Job H0 H1 PState} sched
EDF_schedule is transparent
Expands to: Constant prosa.model.schedule.edf.EDF_schedule
Declared in library prosa.model.schedule.edf, line 57, characters 13-25
@EDF_schedule
     : forall Job : JobType,
       JobDeadline Job -> JobArrival Job -> forall PState : ProcessorState Job, @schedule Job PState -> Prop
```

Body:

```coq
EDF_schedule =
fun (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) =>
forall t : instant, @EDF_at Job H0 H1 PState sched t
     : forall {Job : JobType},
       JobDeadline Job ->
       JobArrival Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

Arguments EDF_schedule {Job H0 H1 PState} sched
```

## Lean

```lean
@Prosa.Model.Schedule.Edf.EDF_schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Model.Schedule.Edf.EDF_schedule.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] [Prosa.Behavior.Job.JobArrival Job] {PState} sched =>
  ∀ (t : Prosa.Behavior.Time.instant), Prosa.Model.Schedule.Edf.EDF_at sched t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Edf_EDF_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_Edf_EDF_schedule@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0
Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                    inst_3)
  (inst_9 : Prosa_Behavior_Job_JobArrival Job
                                                                    inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job inst_3
             PState) =>
forall t : Prosa_Behavior_Time_instant,
Prosa_Model_Schedule_Edf_EDF_at Job inst_3
  inst_6
  inst_9 PState sched t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       SProp

Arguments Prosa_Model_Schedule_Edf_EDF_schedule Job
  inst_3
  inst_6
  inst_9 PState sched
```
