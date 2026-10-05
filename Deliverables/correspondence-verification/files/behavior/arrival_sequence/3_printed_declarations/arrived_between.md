# `arrived_between`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrived_between`
- Lean: `Prosa.Behavior.Arrival_sequence.arrived_between`
- Certificate: `arrived_between_correspondence_certificate`

## Official Rocq

```coq
arrived_between : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> instant -> instant -> bool

arrived_between is not universe polymorphic
Arguments arrived_between {Job H} j t1 t2
arrived_between is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrived_between
Declared in library prosa.behavior.arrival_sequence, line 93, characters 13-28
@arrived_between
     : forall Job : JobType, JobArrival Job -> Equality.sort Job -> instant -> instant -> bool
```

Body:

```coq
arrived_between =
fun (Job : JobType) (H : JobArrival Job) (j : Equality.sort Job) (t1 t2 : instant) =>
t1 <= @job_arrival Job H j < t2
     : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> instant -> instant -> bool

Arguments arrived_between {Job H} j t1 t2
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrived_between : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Arrival_sequence.arrived_between.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] j t1 t2 =>
  decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) && decide (Prosa.Behavior.Job.job_arrival j < t2)
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrived_between
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrived_between@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Bool_and
  (Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j))
     (Nat_decLe t1
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)))
  (Decidable_decide
     (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        t2)
     (Nat_decLt
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        t2))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Behavior_Arrival_sequence_arrived_between Job
  inst_3
  inst_6 j t1 t
```
