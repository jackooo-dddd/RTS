# `generate_jobs_at_unique`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.job_constructor.generate_jobs_at_unique`
- Lean: `Prosa.Implementation.Facts.JobConstructor.generate_jobs_at_unique`
- Certificate: `generate_jobs_at_unique_correspondence`

## Official Rocq

```coq
generate_jobs_at_unique :
forall (tsk : concrete_task) (n : nat) (t : instant), is_true (@uniq Job (generate_jobs_at tsk n t))

generate_jobs_at_unique is not universe polymorphic
Arguments generate_jobs_at_unique tsk n%nat_scope t
generate_jobs_at_unique is opaque
Expands to: Constant prosa.implementation.facts.job_constructor.generate_jobs_at_unique
Declared in library prosa.implementation.facts.job_constructor, line 24, characters 8-31
generate_jobs_at_unique
     : forall (tsk : concrete_task) (n : nat) (t : instant), is_true (@uniq Job (generate_jobs_at tsk n t))
```

## Lean

```lean
Prosa.Implementation.Facts.JobConstructor.generate_jobs_at_unique : ∀
  (tsk : Prosa.Implementation.Definitions.Task.concrete_task) (n : ℕ) (t : Prosa.Behavior.Time.instant),
  (Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at tsk n t).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_JobConstructor_generate_jobs_at_unique
     : forall (tsk : Prosa_Implementation_Definitions_Task_concrete_task) (n : Nat)
         (t : Prosa_Behavior_Time_instant),
       List_Nodup_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
         (Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at tsk n t)
```
