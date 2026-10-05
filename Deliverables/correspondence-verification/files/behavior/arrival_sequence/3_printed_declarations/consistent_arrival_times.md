# `consistent_arrival_times`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.consistent_arrival_times`
- Lean: `Prosa.Behavior.Arrival_sequence.consistent_arrival_times`
- Certificate: `consistent_arrival_times_correspondence_certificate`

## Official Rocq

```coq
consistent_arrival_times : forall {Job : JobType}, JobArrival Job -> arrival_sequence Job -> Prop

consistent_arrival_times is not universe polymorphic
Arguments consistent_arrival_times {Job H} arr_seq
consistent_arrival_times is transparent
Expands to: Constant prosa.behavior.arrival_sequence.consistent_arrival_times
Declared in library prosa.behavior.arrival_sequence, line 56, characters 13-37
@consistent_arrival_times
     : forall Job : JobType, JobArrival Job -> arrival_sequence Job -> Prop
```

Body:

```coq
consistent_arrival_times =
fun (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job) =>
forall (j : Equality.sort Job) (t : instant),
is_true (@arrives_at Job arr_seq j t) -> @job_arrival Job H j = t
     : forall {Job : JobType}, JobArrival Job -> arrival_sequence Job -> Prop

Arguments consistent_arrival_times {Job H} arr_seq
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.consistent_arrival_times : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Behavior.Arrival_sequence.consistent_arrival_times.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] arr_seq =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_at arr_seq j t = true → Prosa.Behavior.Job.job_arrival j = t
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_consistent_arrival_times
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_consistent_arrival_times@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
@eq Bool
  (Prosa_Behavior_Arrival_sequence_arrives_at Job
     inst_3 arr_seq j t)
  Bool_true ->
@eq Prosa_Behavior_Time_instant
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_3
     inst_6 j)
  t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
  inst_3
  inst_6 arr_seq
```
