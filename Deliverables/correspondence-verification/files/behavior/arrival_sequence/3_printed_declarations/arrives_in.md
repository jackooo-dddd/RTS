# `arrives_in`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrives_in`
- Lean: `Prosa.Behavior.Arrival_sequence.arrives_in`
- Certificate: `arrives_in_correspondence_certificate`

## Official Rocq

```coq
arrives_in : forall {Job : JobType}, arrival_sequence Job -> Equality.sort Job -> Prop

arrives_in is not universe polymorphic
Arguments arrives_in {Job} arr_seq j
arrives_in is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrives_in
Declared in library prosa.behavior.arrival_sequence, line 38, characters 13-23
@arrives_in
     : forall Job : JobType, arrival_sequence Job -> Equality.sort Job -> Prop
```

Body:

```coq
arrives_in =
fun (Job : JobType) (arr_seq : arrival_sequence Job) (j : Equality.sort Job) =>
exists t : instant, is_true (j \in @arrivals_at Job arr_seq t)
     : forall {Job : JobType}, arrival_sequence Job -> Equality.sort Job -> Prop

Arguments arrives_in {Job} arr_seq j
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrives_in : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Prop
def Prosa.Behavior.Arrival_sequence.arrives_in.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Prop :=
fun {Job} [DecidableEq Job] arr_seq j => ∃ t, Prosa.Behavior.Arrival_sequence.arrives_at arr_seq j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrives_in
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> SProp
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrives_in@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (j : Job) =>
Exists Prosa_Behavior_Time_instant
  (fun t : Prosa_Behavior_Time_instant =>
   Prosa_Behavior_Arrival_sequence_arrives_at Job
     inst_3 arr_seq j t =
   Bool_true)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> SProp

Arguments Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq a____at____internal__hyg0
```
