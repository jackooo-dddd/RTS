# `arrivals_at`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrivals_at`
- Lean: `Prosa.Behavior.Arrival_sequence.arrivals_at`
- Certificate: `arrivals_at_correspondence_certificate`

## Official Rocq

```coq
arrivals_at : forall {Job : JobType}, arrival_sequence Job -> instant -> seq (Equality.sort Job)

arrivals_at is not universe polymorphic
Arguments arrivals_at {Job} arr_seq t
arrivals_at is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrivals_at
Declared in library prosa.behavior.arrival_sequence, line 30, characters 13-24
@arrivals_at
     : forall Job : JobType, arrival_sequence Job -> instant -> seq (Equality.sort Job)
```

Body:

```coq
arrivals_at =
fun (Job : JobType) (arr_seq : arrival_sequence Job) => [eta arr_seq]
     : forall {Job : JobType}, arrival_sequence Job -> instant -> seq (Equality.sort Job)

Arguments arrivals_at {Job} arr_seq t
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrivals_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → List Job
def Prosa.Behavior.Arrival_sequence.arrivals_at.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] arr_seq t => arr_seq t
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrivals_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrivals_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (t : Prosa_Behavior_Time_instant) =>
arr_seq t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Behavior_Arrival_sequence_arrivals_at Job
  inst_3 arr_seq t
```
