# `arrivals_between`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrivals_between`
- Lean: `Prosa.Behavior.Arrival_sequence.arrivals_between`
- Certificate: `arrivals_between_correspondence_certificate`

## Official Rocq

```coq
arrivals_between :
forall {Job : JobType}, arrival_sequence Job -> instant -> instant -> seq (Equality.sort Job)

arrivals_between is not universe polymorphic
Arguments arrivals_between {Job} arr_seq t1 t2
arrivals_between is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrivals_between
Declared in library prosa.behavior.arrival_sequence, line 112, characters 13-29
@arrivals_between
     : forall Job : JobType, arrival_sequence Job -> instant -> instant -> seq (Equality.sort Job)
```

Body:

```coq
arrivals_between =
fun (Job : JobType) (arr_seq : arrival_sequence Job) (t1 t2 : instant) =>
\cat_(t1<=t<t2)@arrivals_at Job arr_seq t
     : forall {Job : JobType}, arrival_sequence Job -> instant -> instant -> seq (Equality.sort Job)

Arguments arrivals_between {Job} arr_seq t1 t2
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrivals_between : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → List Job
def Prosa.Behavior.Arrival_sequence.arrivals_between.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] arr_seq t1 t2 =>
  Prosa.Util.Notation.bigCat t1 t2 (Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrivals_between
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrivals_between@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Util_Notation_bigCat Job t1 t2
  (Prosa_Behavior_Arrival_sequence_arrivals_at Job
     inst_3 arr_seq)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Behavior_Arrival_sequence_arrivals_between Job
  inst_3 arr_seq t1 
  t2
```
