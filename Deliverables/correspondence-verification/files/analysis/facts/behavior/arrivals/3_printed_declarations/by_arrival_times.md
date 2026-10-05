# `by_arrival_times`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.behavior.arrivals.by_arrival_times`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times`
- Certificate: `by_arrival_times_correspondence`

## Official Rocq

```coq
by_arrival_times : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> Equality.sort Job -> bool

by_arrival_times is not universe polymorphic
Arguments by_arrival_times {Job H} j1 j2
by_arrival_times is transparent
Expands to: Constant prosa.analysis.facts.behavior.arrivals.by_arrival_times
Declared in library prosa.analysis.facts.behavior.arrivals, line 419, characters 15-31
@by_arrival_times
     : forall Job : JobType, JobArrival Job -> Equality.sort Job -> Equality.sort Job -> bool
```

Body:

```coq
by_arrival_times =
fun (Job : JobType) (H : JobArrival Job) (j1 j2 : Equality.sort Job) =>
@job_arrival Job H j1 <= @job_arrival Job H j2
     : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> Equality.sort Job -> bool

Arguments by_arrival_times {Job H} j1 j2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Job → Job → Bool
def Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Job → Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] j1 j2 =>
  decide (Prosa.Behavior.Job.job_arrival j1 ≤ Prosa.Behavior.Job.job_arrival j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Job -> Job -> Bool
```

Body:

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (j1 j2 : Job) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j1)
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j2))
  (Nat_decLe
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j1)
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j2))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Job -> Job -> Bool

Arguments Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times Job
  inst_3
  inst_6 j1 
  j2
```
