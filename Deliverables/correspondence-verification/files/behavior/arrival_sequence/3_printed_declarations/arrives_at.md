# `arrives_at`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrives_at`
- Lean: `Prosa.Behavior.Arrival_sequence.arrives_at`
- Certificate: `arrives_at_correspondence_certificate`

## Official Rocq

```coq
arrives_at : forall {Job : JobType}, arrival_sequence Job -> Equality.sort Job -> instant -> bool

arrives_at is not universe polymorphic
Arguments arrives_at {Job} arr_seq j t
arrives_at is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrives_at
Declared in library prosa.behavior.arrival_sequence, line 34, characters 13-23
@arrives_at
     : forall Job : JobType, arrival_sequence Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
arrives_at =
fun (Job : JobType) (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t : instant) =>
j \in @arrivals_at Job arr_seq t
     : forall {Job : JobType}, arrival_sequence Job -> Equality.sort Job -> instant -> bool

Arguments arrives_at {Job} arr_seq j t
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrives_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Arrival_sequence.arrives_at.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] arr_seq j t => decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq t)
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrives_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrives_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Decidable_decide
  (Membership_mem Job (List Job) (List_instMembership Job)
     (Prosa_Behavior_Arrival_sequence_arrivals_at Job
        inst_3 arr_seq t)
     j)
  (List_instDecidableMemOfLawfulBEq Job
     (instBEqOfDecidableEq Job inst_3)
     (instLawfulBEq Job inst_3) j
     (Prosa_Behavior_Arrival_sequence_arrivals_at Job
        inst_3 arr_seq t))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Behavior_Arrival_sequence_arrives_at Job
  inst_3 arr_seq j 
  t
```
