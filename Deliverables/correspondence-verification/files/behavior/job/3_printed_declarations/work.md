# `work`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.job.work`
- Lean: `Prosa.Behavior.Job.work`
- Certificate: ``

## Official Rocq

```coq
work : Set

work is not universe polymorphic
work is transparent
Expands to: Constant prosa.behavior.job.work
Declared in library prosa.behavior.job, line 13, characters 11-15
work
     : Set
```

Body:

```coq
work = nat
     : Set
```

## Lean

```lean
Prosa.Behavior.Job.work : Type
```

Body:

```lean
@[reducible] def Prosa.Behavior.Job.work : Type :=
ℕ
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Job_work
     : Type
```

Body:

```coq
Prosa_Behavior_Job_work@{} = Nat
     : Type
```
