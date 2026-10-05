# `suspension_has_passed`

- Kind (Rocq): Definition
- Rocq: `prosa.model.readiness.suspension.suspension_has_passed`
- Lean: `Prosa.Model.Readiness.Suspension.suspension_has_passed`
- Certificate: `suspension_has_passed_correspondence`

## Official Rocq

```coq
suspension_has_passed :
forall {Job : JobType} {PState : ProcessorState Job},
JobArrival Job -> JobSuspension Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

suspension_has_passed is not universe polymorphic
Arguments suspension_has_passed {Job PState H H1} sched j t
suspension_has_passed is transparent
Expands to: Constant prosa.model.readiness.suspension.suspension_has_passed
Declared in library prosa.model.readiness.suspension, line 39, characters 13-34
@suspension_has_passed
     : forall (Job : JobType) (PState : ProcessorState Job),
       JobArrival Job -> JobSuspension Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
suspension_has_passed =
fun (Job : JobType) (PState : ProcessorState Job) (H : JobArrival Job) (H1 : JobSuspension Job)
  (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant) =>
let delay := @job_suspension Job H1 j (@service Job PState sched j t) in
(@job_arrival Job H j + delay <= t) && @no_progress_for Job PState sched j t delay
     : forall {Job : JobType} {PState : ProcessorState Job},
       JobArrival Job -> JobSuspension Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments suspension_has_passed {Job PState H H1} sched j t
```

## Lean

```lean
@Prosa.Model.Readiness.Suspension.suspension_has_passed : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [Prosa.Behavior.Job.JobArrival Job] →
        [Prosa.Model.Readiness.Suspension.JobSuspension Job] →
          Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Model.Readiness.Suspension.suspension_has_passed.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [Prosa.Behavior.Job.JobArrival Job] →
        [Prosa.Model.Readiness.Suspension.JobSuspension Job] →
          Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Model.Readiness.Suspension.JobSuspension Job] sched j t =>
  have delay := Prosa.Model.Readiness.Suspension.job_suspension j (Prosa.Behavior.Service.service sched j t);
  decide (Prosa.Behavior.Job.job_arrival j + delay ≤ t) &&
    Prosa.Analysis.Definitions.Progress.no_progress_for sched j t delay
```

## Lean, imported into Rocq

```coq
Prosa_Model_Readiness_Suspension_suspension_has_passed
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Readiness_Suspension_suspension_has_passed@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_8 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (inst_14 : Prosa_Model_Readiness_Suspension_JobSuspension
                                                                              Job
                                                                              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
let delay :=
  Prosa_Model_Readiness_Suspension_JobSuspension_job_suspension Job
    inst_3
    inst_14 j
    (Prosa_Behavior_Service_service Job inst_3
       PState sched j t)
  in
Bool_and
  (Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
           (Prosa_Behavior_Job_JobArrival_job_arrival Job
              inst_3
              inst_8 j)
           delay)
        t)
     (Nat_decLe
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
           (Prosa_Behavior_Job_JobArrival_job_arrival Job
              inst_3
              inst_8 j)
           delay)
        t))
  (Prosa_Analysis_Definitions_Progress_no_progress_for Job
     inst_3 PState sched j t delay)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Readiness_Suspension_suspension_has_passed Job
  inst_3 PState
  inst_8
  inst_14 sched j 
  t
```
