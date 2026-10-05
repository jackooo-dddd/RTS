# `generate_jobs_at`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.job_constructor.generate_jobs_at`
- Lean: `Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at`
- Certificate: `generate_jobs_at_correspondence`

## Official Rocq

```coq
generate_jobs_at : concrete_task -> nat -> instant -> seq (Equality.sort Job)

generate_jobs_at is not universe polymorphic
Arguments generate_jobs_at tsk n%nat_scope t
generate_jobs_at is transparent
Expands to: Constant prosa.implementation.definitions.job_constructor.generate_jobs_at
Declared in library prosa.implementation.definitions.job_constructor, line 27, characters 11-27
generate_jobs_at
     : concrete_task -> nat -> instant -> seq (Equality.sort Job)
```

Body:

```coq
generate_jobs_at =
fun (tsk : concrete_task) (n : nat) (t : instant) => [seq generate_job_at tsk t i | i <- iota 0 n]
     : concrete_task -> nat -> instant -> seq (Equality.sort Job)

Arguments generate_jobs_at tsk n%nat_scope t
```

## Lean

```lean
Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at : Prosa.Implementation.Definitions.Task.concrete_task →
  ℕ → Prosa.Behavior.Time.instant → List Prosa.Implementation.Definitions.JobConstructor.Job
```

Body:

```lean
def Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at : Prosa.Implementation.Definitions.Task.concrete_task →
  ℕ → Prosa.Behavior.Time.instant → List Prosa.Implementation.Definitions.JobConstructor.Job :=
fun tsk n t => List.map (Prosa.Implementation.Definitions.JobConstructor.generate_job_at tsk t) (List.range' 0 n)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Nat -> Prosa_Behavior_Time_instant -> List_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
```

Body:

```coq
Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at@{} =
fun (tsk : Prosa_Implementation_Definitions_Task_concrete_task) (n : Nat) (t : Prosa_Behavior_Time_instant) =>
List_map_inst3 Nat Prosa_Implementation_Definitions_JobConstructor_Job
  (Prosa_Implementation_Definitions_JobConstructor_generate_job_at tsk t)
  (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) n (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Nat -> Prosa_Behavior_Time_instant -> List_inst1 Prosa_Implementation_Definitions_JobConstructor_Job

Arguments Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at tsk n%_Nat_scope t
```
