# `arrival_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.arrival_sequence.arrival_sequence`
- Lean: `Prosa.Behavior.Arrival_sequence.arrival_sequence`
- Certificate: `arrival_sequence_correspondence_certificate`

## Official Rocq

```coq
arrival_sequence : JobType -> Type

arrival_sequence is not universe polymorphic
Arguments arrival_sequence Job
arrival_sequence is transparent
Expands to: Constant prosa.behavior.arrival_sequence.arrival_sequence
Declared in library prosa.behavior.arrival_sequence, line 16, characters 13-29
arrival_sequence
     : JobType -> Type
```

Body:

```coq
arrival_sequence = fun Job : JobType => instant -> seq (Equality.sort Job)
     : JobType -> Type

Arguments arrival_sequence Job
```

## Lean

```lean
Prosa.Behavior.Arrival_sequence.arrival_sequence : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
def Prosa.Behavior.Arrival_sequence.arrival_sequence.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [DecidableEq Job] → Type u_1 :=
fun Job [DecidableEq Job] => Prosa.Behavior.Time.instant → List Job
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Arrival_sequence_arrival_sequence
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```

Body:

```coq
Prosa_Behavior_Arrival_sequence_arrival_sequence@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType) (_ : DecidableEq Job) => Prosa_Behavior_Time_instant -> List Job
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type

Arguments Prosa_Behavior_Arrival_sequence_arrival_sequence Job
  inst_3
```
