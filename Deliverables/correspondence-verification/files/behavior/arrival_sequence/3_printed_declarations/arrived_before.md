# `arrived_before`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrived_before`
- Lean: `Prosa.Behavior.Arrival_sequence.arrived_before`
- Certificate: `arrived_before_correspondence_certificate`

## Official Rocq

```coq
arrived_before : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> instant -> bool

arrived_before is not universe polymorphic
Arguments arrived_before {Job H} j t
arrived_before is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrived_before
Declared in library prosa.behavior.arrival_sequence, line 89, characters 13-27
@arrived_before
     : forall Job : JobType, JobArrival Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
arrived_before =
fun (Job : JobType) (H : JobArrival Job) (j : Equality.sort Job) => [eta leq (@job_arrival Job H j).+1]
     : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> instant -> bool

Arguments arrived_before {Job H} j t
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrived_before : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Arrival_sequence.arrived_before.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] j t => decide (Prosa.Behavior.Job.job_arrival j < t)
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrived_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrived_before@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Decidable_decide
  (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j)
     t)
  (Nat_decLt
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j)
     t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Behavior_Arrival_sequence_arrived_before Job
  inst_3
  inst_6 j t
```
