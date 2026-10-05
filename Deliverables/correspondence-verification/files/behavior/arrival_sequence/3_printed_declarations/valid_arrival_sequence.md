# `valid_arrival_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.valid_arrival_sequence`
- Lean: `Prosa.Behavior.Arrival_sequence.valid_arrival_sequence`
- Certificate: `valid_arrival_sequence_correspondence_certificate`

## Official Rocq

```coq
valid_arrival_sequence : forall {Job : JobType}, JobArrival Job -> arrival_sequence Job -> Prop

valid_arrival_sequence is not universe polymorphic
Arguments valid_arrival_sequence {Job H} arr_seq
valid_arrival_sequence is transparent
Expands to: Constant prosa.behavior.arrival_sequence.valid_arrival_sequence
Declared in library prosa.behavior.arrival_sequence, line 66, characters 13-35
@valid_arrival_sequence
     : forall Job : JobType, JobArrival Job -> arrival_sequence Job -> Prop
```

Body:

```coq
valid_arrival_sequence =
fun (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job) =>
@consistent_arrival_times Job H arr_seq /\ @arrival_sequence_uniq Job arr_seq
     : forall {Job : JobType}, JobArrival Job -> arrival_sequence Job -> Prop

Arguments valid_arrival_sequence {Job H} arr_seq
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.valid_arrival_sequence : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Behavior.Arrival_sequence.valid_arrival_sequence.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] arr_seq =>
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq ∧
    Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_valid_arrival_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_valid_arrival_sequence@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
And
  (Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
     inst_3
     inst_6 arr_seq)
  (Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
     inst_3 arr_seq)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
  inst_3
  inst_6 arr_seq
```
