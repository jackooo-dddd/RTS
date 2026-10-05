# `job_generation_valid_jobs`

- Kind (Rocq): Corollary
- Rocq: `prosa.implementation.facts.job_constructor.job_generation_valid_jobs`
- Lean: `Prosa.Implementation.Facts.JobConstructor.job_generation_valid_jobs`
- Certificate: `job_generation_valid_jobs_correspondence`

## Official Rocq

```coq
job_generation_valid_jobs :
forall (tsk : concrete_task) (n : nat) (t : instant) (j : Equality.sort Job),
is_true (j \in generate_jobs_at tsk n t) ->
job_task j = tsk /\ job_arrival j = t /\ is_true (job_cost j <= task_cost tsk)

job_generation_valid_jobs is not universe polymorphic
Arguments job_generation_valid_jobs tsk n%nat_scope t j _
job_generation_valid_jobs is opaque
Expands to: Constant prosa.implementation.facts.job_constructor.job_generation_valid_jobs
Declared in library prosa.implementation.facts.job_constructor, line 73, characters 12-37
job_generation_valid_jobs
     : forall (tsk : concrete_task) (n : nat) (t : instant) (j : Equality.sort Job),
       is_true (j \in generate_jobs_at tsk n t) ->
       job_task j = tsk /\ job_arrival j = t /\ is_true (job_cost j <= task_cost tsk)
```

## Lean

```lean
Prosa.Implementation.Facts.JobConstructor.job_generation_valid_jobs : ∀
  (tsk : Prosa.Implementation.Definitions.Task.concrete_task) (n : ℕ) (t : Prosa.Behavior.Time.instant)
  (j : Prosa.Implementation.Definitions.JobConstructor.Job),
  decide (j ∈ Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at tsk n t) = true →
    j.job_task = tsk ∧ j.job_arrival = t ∧ j.job_cost ≤ tsk.task_cost
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_JobConstructor_job_generation_valid_jobs
     : forall (tsk : Prosa_Implementation_Definitions_Task_concrete_task) (n : Nat)
         (t : Prosa_Behavior_Time_instant) (j : Prosa_Implementation_Definitions_JobConstructor_Job),
       @eq Bool
         (Decidable_decide
            (Membership_mem_inst3 Prosa_Implementation_Definitions_JobConstructor_Job
               (List_inst1 Prosa_Implementation_Definitions_JobConstructor_Job)
               (List_instMembership_inst1 Prosa_Implementation_Definitions_JobConstructor_Job)
               (Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at tsk n t) j)
            (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
               (instBEqOfDecidableEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
               (instLawfulBEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
               j (Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at tsk n t)))
         Bool_true ->
       And
         (@eq Prosa_Implementation_Definitions_Task_concrete_task
            (Prosa_Implementation_Definitions_Task_concrete_job_job_task j) tsk)
         (And
            (@eq Prosa_Behavior_Time_instant
               (Prosa_Implementation_Definitions_Task_concrete_job_job_arrival j) t)
            (LE_le_inst1 Nat instLENat (Prosa_Implementation_Definitions_Task_concrete_job_job_cost j)
               (Prosa_Implementation_Definitions_Task_concrete_task_task_cost tsk)))
```
