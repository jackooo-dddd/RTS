# `arrivals_before`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrivals_before`
- Lean: `Prosa.Behavior.Arrival_sequence.arrivals_before`
- Certificate: `arrivals_before_correspondence_certificate`

## Official Rocq

```coq
arrivals_before : forall {Job : JobType}, arrival_sequence Job -> instant -> seq (Equality.sort Job)

arrivals_before is not universe polymorphic
Arguments arrivals_before {Job} arr_seq t
arrivals_before is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrivals_before
Declared in library prosa.behavior.arrival_sequence, line 119, characters 13-28
@arrivals_before
     : forall Job : JobType, arrival_sequence Job -> instant -> seq (Equality.sort Job)
```

Body:

```coq
arrivals_before =
fun (Job : JobType) (arr_seq : arrival_sequence Job) => [eta @arrivals_between Job arr_seq 0]
     : forall {Job : JobType}, arrival_sequence Job -> instant -> seq (Equality.sort Job)

Arguments arrivals_before {Job} arr_seq t
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrivals_before : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → List Job
def Prosa.Behavior.Arrival_sequence.arrivals_before.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] arr_seq t => Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 t
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrivals_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrivals_before@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Behavior_Arrival_sequence_arrivals_between Job
  inst_3 arr_seq
  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Behavior_Arrival_sequence_arrivals_before Job
  inst_3 arr_seq t
```
