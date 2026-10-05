# `arrival_sequence_uniq`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrival_sequence_uniq`
- Lean: `Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq`
- Certificate: `arrival_sequence_uniq_correspondence_certificate`

## Official Rocq

```coq
arrival_sequence_uniq : forall {Job : JobType}, arrival_sequence Job -> Prop

arrival_sequence_uniq is not universe polymorphic
Arguments arrival_sequence_uniq {Job} arr_seq
arrival_sequence_uniq is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrival_sequence_uniq
Declared in library prosa.behavior.arrival_sequence, line 62, characters 13-34
@arrival_sequence_uniq
     : forall Job : JobType, arrival_sequence Job -> Prop
```

Body:

```coq
arrival_sequence_uniq =
fun (Job : JobType) (arr_seq : arrival_sequence Job) =>
forall t : instant, is_true (@uniq Job (@arrivals_at Job arr_seq t))
     : forall {Job : JobType}, arrival_sequence Job -> Prop

Arguments arrival_sequence_uniq {Job} arr_seq
```

## Lean

```lean
@Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] arr_seq =>
  ∀ (t : Prosa.Behavior.Time.instant), (Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq t).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
forall t : Prosa_Behavior_Time_instant,
List_Nodup Job
  (Prosa_Behavior_Arrival_sequence_arrivals_at Job
     inst_3 arr_seq t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
  inst_3 arr_seq
```
