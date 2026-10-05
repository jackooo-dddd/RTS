# `job_generation_valid_number`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.job_constructor.job_generation_valid_number`
- Lean: `Prosa.Implementation.Facts.JobConstructor.job_generation_valid_number`
- Certificate: `job_generation_valid_number_correspondence`

## Official Rocq

```coq
job_generation_valid_number :
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (n : nat) (t : instant),
is_true (tsk \in ts) -> @size (Equality.sort Job) (generate_jobs_at tsk n t) = n

job_generation_valid_number is not universe polymorphic
Arguments job_generation_valid_number ts%seq_scope tsk n%nat_scope t _
job_generation_valid_number is opaque
Expands to: Constant prosa.implementation.facts.job_constructor.job_generation_valid_number
Declared in library prosa.implementation.facts.job_constructor, line 15, characters 8-35
job_generation_valid_number
     : forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (n : nat) (t : instant),
       is_true (tsk \in ts) -> @size (Equality.sort Job) (generate_jobs_at tsk n t) = n
```

## Lean

```lean
Prosa.Implementation.Facts.JobConstructor.job_generation_valid_number : ∀
  (ts : List Prosa.Implementation.Definitions.JobConstructor.Task)
  (tsk : Prosa.Implementation.Definitions.JobConstructor.Task) (n : ℕ) (t : Prosa.Behavior.Time.instant),
  decide (tsk ∈ ts) = true → (Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at tsk n t).length = n
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_JobConstructor_job_generation_valid_number
     : forall (ts : List_inst1 Prosa_Implementation_Definitions_JobConstructor_Task)
         (tsk : Prosa_Implementation_Definitions_JobConstructor_Task) (n : Nat)
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem_inst3 Prosa_Implementation_Definitions_JobConstructor_Task
               (List_inst1 Prosa_Implementation_Definitions_JobConstructor_Task)
               (List_instMembership_inst1 Prosa_Implementation_Definitions_JobConstructor_Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Task
               (instBEqOfDecidableEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Task
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task)
               (instLawfulBEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Task
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task)
               tsk ts))
         Bool_true ->
       @eq Nat
         (List_length_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
            (Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at tsk n t))
         n
```
