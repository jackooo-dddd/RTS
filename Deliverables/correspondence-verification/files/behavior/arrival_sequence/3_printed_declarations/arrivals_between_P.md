# `arrivals_between_P`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrivals_between_P`
- Lean: `Prosa.Behavior.Arrival_sequence.arrivals_between_P`
- Certificate: `arrivals_between_P_correspondence_certificate`

## Official Rocq

```coq
arrivals_between_P :
forall {Job : JobType},
arrival_sequence Job -> (Equality.sort Job -> bool) -> instant -> instant -> seq (Equality.sort Job)

arrivals_between_P is not universe polymorphic
Arguments arrivals_between_P {Job} arr_seq P%function_scope t1 t2
arrivals_between_P is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrivals_between_P
Declared in library prosa.behavior.arrival_sequence, line 123, characters 13-31
@arrivals_between_P
     : forall Job : JobType,
       arrival_sequence Job -> (Equality.sort Job -> bool) -> instant -> instant -> seq (Equality.sort Job)
```

Body:

```coq
arrivals_between_P =
fun (Job : JobType) (arr_seq : arrival_sequence Job) (P : Equality.sort Job -> bool) (t1 t2 : instant) =>
     : forall {Job : JobType},
       arrival_sequence Job -> (Equality.sort Job -> bool) -> instant -> instant -> seq (Equality.sort Job)

Arguments arrivals_between_P {Job} arr_seq P%function_scope t1 t2
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrivals_between_P : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
      (Job → Bool) → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → List Job
def Prosa.Behavior.Arrival_sequence.arrivals_between_P.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
      (Job → Bool) → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] arr_seq P t1 t2 =>
  List.filter P (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrivals_between_P
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       (Job -> Bool) -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrivals_between_P@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (P : Job -> Bool) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_filter Job P
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_3 arr_seq t1 t2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       (Job -> Bool) -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
  inst_3 arr_seq P%_function_scope 
  t1 t2
```
