# `EDF_at`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.edf.EDF_at`
- Lean: `Prosa.Model.Schedule.Edf.EDF_at`
- Certificate: `EDF_at_correspondence`

## Official Rocq

```coq
EDF_at :
forall {Job : JobType},
JobDeadline Job ->
JobArrival Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> instant -> Prop

EDF_at is not universe polymorphic
Arguments EDF_at {Job H0 H1 PState} sched t
EDF_at is transparent
Expands to: Constant prosa.model.schedule.edf.EDF_at
Declared in library prosa.model.schedule.edf, line 44, characters 13-19
@EDF_at
     : forall Job : JobType,
       JobDeadline Job ->
       JobArrival Job -> forall PState : ProcessorState Job, @schedule Job PState -> instant -> Prop
```

Body:

```coq
EDF_at =
fun (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (t : instant) =>
forall j : Equality.sort Job,
is_true (@scheduled_at Job PState sched j t) ->
forall (t' : instant) (j' : Equality.sort Job),
is_true (t <= t') ->
is_true (@scheduled_at Job PState sched j' t') ->
is_true (@job_arrival Job H1 j' <= t) -> is_true (@job_deadline Job H0 j <= @job_deadline Job H0 j')
     : forall {Job : JobType},
       JobDeadline Job ->
       JobArrival Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> instant -> Prop

Arguments EDF_at {Job H0 H1 PState} sched t
```

## Lean

```lean
@Prosa.Model.Schedule.Edf.EDF_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prop
def Prosa.Model.Schedule.Edf.EDF_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] [Prosa.Behavior.Job.JobArrival Job] {PState} sched t =>
  ∀ (j : Job),
    Prosa.Behavior.Service.scheduled_at sched j t = true →
      ∀ (t' : Prosa.Behavior.Time.instant) (j' : Job),
        t ≤ t' →
          Prosa.Behavior.Service.scheduled_at sched j' t' = true →
            Prosa.Behavior.Job.job_arrival j' ≤ t →
              Prosa.Behavior.Job.job_deadline j ≤ Prosa.Behavior.Job.job_deadline j'
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Edf_EDF_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Model_Schedule_Edf_EDF_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0
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
             PState)
  (t : Prosa_Behavior_Time_instant) =>
forall j : Job,
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job inst_3
     PState sched j t)
  Bool_true ->
forall (t' : Prosa_Behavior_Time_instant) (j' : Job),
LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t' ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job inst_3
     PState sched j' t')
  Bool_true ->
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_3
     inst_9 j')
  t ->
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (Prosa_Behavior_Job_JobDeadline_job_deadline Job
     inst_3
     inst_6 j)
  (Prosa_Behavior_Job_JobDeadline_job_deadline Job
     inst_3
     inst_6 j')
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Model_Schedule_Edf_EDF_at Job inst_3
  inst_6
  inst_9 PState sched t
```
