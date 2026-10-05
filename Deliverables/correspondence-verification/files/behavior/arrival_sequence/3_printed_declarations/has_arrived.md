# `has_arrived`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.has_arrived`
- Lean: `Prosa.Behavior.Arrival_sequence.has_arrived`
- Certificate: `has_arrived_correspondence_certificate`

## Official Rocq

```coq
has_arrived : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> instant -> bool

has_arrived is not universe polymorphic
Arguments has_arrived {Job H} j t
has_arrived is transparent
Expands to: Constant prosa.behavior.arrival_sequence.has_arrived
Declared in library prosa.behavior.arrival_sequence, line 85, characters 13-24
@has_arrived
     : forall Job : JobType, JobArrival Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
has_arrived =
fun (Job : JobType) (H : JobArrival Job) (j : Equality.sort Job) => [eta leq (@job_arrival Job H j)]
     : forall {Job : JobType}, JobArrival Job -> Equality.sort Job -> instant -> bool

Arguments has_arrived {Job H} j t
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.has_arrived : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Arrival_sequence.has_arrived.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] j t => decide (Prosa.Behavior.Job.job_arrival j ≤ t)
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_has_arrived
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_has_arrived@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j)
     t)
  (Nat_decLe
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j)
     t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Behavior_Arrival_sequence_has_arrived Job
  inst_3
  inst_6 j t
```
