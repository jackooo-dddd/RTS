# `suspended`

- Kind (Rocq): Definition
- Rocq: `prosa.model.readiness.suspension.suspended`
- Lean: `Prosa.Model.Readiness.Suspension.suspended`
- Certificate: `suspended_correspondence`

## Official Rocq

```coq
suspended :
forall {Job : JobType} {PState : ProcessorState Job},
JobArrival Job ->
JobCost Job -> JobSuspension Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

suspended is not universe polymorphic
Arguments suspended {Job PState H H0 H1} sched j t
suspended is transparent
Expands to: Constant prosa.model.readiness.suspension.suspended
Declared in library prosa.model.readiness.suspension, line 45, characters 13-22
@suspended
     : forall (Job : JobType) (PState : ProcessorState Job),
       JobArrival Job ->
       JobCost Job -> JobSuspension Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
suspended =
fun (Job : JobType) (PState : ProcessorState Job) (H : JobArrival Job) (H0 : JobCost Job)
  (H1 : JobSuspension Job) (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t : instant) =>
~~ @suspension_has_passed Job PState H H1 sched j t && @pending Job PState sched H0 H j t
     : forall {Job : JobType} {PState : ProcessorState Job},
       JobArrival Job ->
       JobCost Job -> JobSuspension Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments suspended {Job PState H H0 H1} sched j t
```

## Lean

```lean
@Prosa.Model.Readiness.Suspension.suspended : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [Prosa.Behavior.Job.JobArrival Job] →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Model.Readiness.Suspension.JobSuspension Job] →
            Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Model.Readiness.Suspension.suspended.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [Prosa.Behavior.Job.JobArrival Job] →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Model.Readiness.Suspension.JobSuspension Job] →
            Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Model.Readiness.Suspension.JobSuspension Job] sched j t =>
  !Prosa.Model.Readiness.Suspension.suspension_has_passed sched j t && Prosa.Behavior.Service.pending sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Readiness_Suspension_suspended
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Readiness_Suspension_suspended@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_8 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (inst_11 : Prosa_Behavior_Job_JobCost Job
                                                                              inst_3)
  (inst_14 : Prosa_Model_Readiness_Suspension_JobSuspension
                                                                              Job
                                                                              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_and
  (Bool_not
     (Prosa_Model_Readiness_Suspension_suspension_has_passed Job
        inst_3 PState
        inst_8
        inst_14 sched j t))
  (Prosa_Behavior_Service_pending Job inst_3
     PState sched inst_11
     inst_8 j t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Readiness_Suspension_suspended Job
  inst_3 PState
  inst_8
  inst_11
  inst_14 sched j 
  t
```
