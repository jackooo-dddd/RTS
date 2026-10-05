# `is_released`

- Kind (Rocq): Definition
- Rocq: `prosa.model.readiness.jitter.is_released`
- Lean: `Prosa.Model.Readiness.Jitter.is_released`
- Certificate: `is_released_correspondence`

## Official Rocq

```coq
is_released : forall {Job : JobType}, JobArrival Job -> JobJitter Job -> Equality.sort Job -> instant -> bool

is_released is not universe polymorphic
Arguments is_released {Job H H1} j t
is_released is transparent
Expands to: Constant prosa.model.readiness.jitter.is_released
Declared in library prosa.model.readiness.jitter, line 31, characters 13-24
@is_released
     : forall Job : JobType, JobArrival Job -> JobJitter Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
is_released =
fun (Job : JobType) (H : JobArrival Job) (H1 : JobJitter Job) (j : Equality.sort Job) =>
     : forall {Job : JobType}, JobArrival Job -> JobJitter Job -> Equality.sort Job -> instant -> bool

Arguments is_released {Job H H1} j t
```

## Lean

```lean
@Prosa.Model.Readiness.Jitter.is_released : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Model.Readiness.Jitter.JobJitter Job] → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Readiness.Jitter.is_released.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Model.Readiness.Jitter.JobJitter Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Model.Readiness.Jitter.JobJitter Job] j t =>
  decide (Prosa.Behavior.Job.job_arrival j + Prosa.Model.Readiness.Jitter.job_jitter j ≤ t)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Readiness_Jitter_is_released
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Readiness_Jitter_is_released@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                         inst_3)
  (inst_9 : Prosa_Model_Readiness_Jitter_JobJitter
                                                                         Job
                                                                         inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        (Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job
           inst_3
           inst_9 j))
     t)
  (Nat_decLe
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        (Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job
           inst_3
           inst_9 j))
     t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Readiness_Jitter_is_released Job
  inst_3
  inst_6
  inst_9 j t
```
