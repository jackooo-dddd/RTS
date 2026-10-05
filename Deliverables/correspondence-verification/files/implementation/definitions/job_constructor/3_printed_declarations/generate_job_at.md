# `generate_job_at`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.job_constructor.generate_job_at`
- Lean: `Prosa.Implementation.Definitions.JobConstructor.generate_job_at`
- Certificate: `generate_job_at_correspondence`

## Official Rocq

```coq
generate_job_at : concrete_task -> instant -> nat -> Equality.sort Job

generate_job_at is not universe polymorphic
Arguments generate_job_at tsk t id%nat_scope
generate_job_at is transparent
Expands to: Constant prosa.implementation.definitions.job_constructor.generate_job_at
Declared in library prosa.implementation.definitions.job_constructor, line 18, characters 11-26
generate_job_at
     : concrete_task -> instant -> nat -> Equality.sort Job
```

Body:

```coq
generate_job_at =
fun (tsk : concrete_task) (t : instant) (id : nat) =>
{|
  job_id := id;
  job_arrival := t;
  job_cost := task_cost tsk;
  job_deadline := t + task_deadline tsk;
  job_task := tsk
|}
     : concrete_task -> instant -> nat -> Equality.sort Job

Arguments generate_job_at tsk t id%nat_scope
```

## Lean

```lean
Prosa.Implementation.Definitions.JobConstructor.generate_job_at : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Behavior.Time.instant → ℕ → Prosa.Implementation.Definitions.JobConstructor.Job
```

Body:

```lean
def Prosa.Implementation.Definitions.JobConstructor.generate_job_at : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Behavior.Time.instant → ℕ → Prosa.Implementation.Definitions.JobConstructor.Job :=
fun tsk t id =>
  { job_id := id, job_arrival := t, job_cost := tsk.task_cost, job_deadline := t + tsk.task_deadline, job_task := tsk }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_JobConstructor_generate_job_at
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Prosa_Behavior_Time_instant -> Nat -> Prosa_Implementation_Definitions_JobConstructor_Job
```

Body:

```coq
Prosa_Implementation_Definitions_JobConstructor_generate_job_at@{} =
fun (tsk : Prosa_Implementation_Definitions_Task_concrete_task) (t : Prosa_Behavior_Time_instant) (id : Nat) =>
Prosa_Implementation_Definitions_Task_concrete_job_mk id t
  (Prosa_Implementation_Definitions_Task_concrete_task_task_cost tsk)
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
     (Prosa_Implementation_Definitions_Task_concrete_task_task_deadline tsk))
  tsk
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Prosa_Behavior_Time_instant -> Nat -> Prosa_Implementation_Definitions_JobConstructor_Job

Arguments Prosa_Implementation_Definitions_JobConstructor_generate_job_at tsk t id%_Nat_scope
```
