# `job_arrival_consistent`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.job_constructor.job_arrival_consistent`
- Lean: `Prosa.Implementation.Facts.JobConstructor.job_arrival_consistent`
- Certificate: `job_arrival_consistent_correspondence`

## Official Rocq

```coq
job_arrival_consistent :
forall (ts : seq (Equality.sort Task)) (j : Equality.sort Job) (t : instant),
is_true
  (j
     \in @arrivals_at Job
           (@concrete_arrival_sequence task_concrete_task__canonical__eqtype_Equality Job ConcreteMaxArrivals
              generate_jobs_at ts)
           t) ->
job_arrival j = t

job_arrival_consistent is not universe polymorphic
Arguments job_arrival_consistent ts%seq_scope j t _
job_arrival_consistent is opaque
Expands to: Constant prosa.implementation.facts.job_constructor.job_arrival_consistent
Declared in library prosa.implementation.facts.job_constructor, line 40, characters 8-30
job_arrival_consistent
     : forall (ts : seq (Equality.sort Task)) (j : Equality.sort Job) (t : instant),
       is_true
         (j
            \in @arrivals_at Job
                  (@concrete_arrival_sequence task_concrete_task__canonical__eqtype_Equality Job
                     ConcreteMaxArrivals generate_jobs_at ts)
                  t) ->
       job_arrival j = t
```

## Lean

```lean
Prosa.Implementation.Facts.JobConstructor.job_arrival_consistent : ∀
  (ts : List Prosa.Implementation.Definitions.JobConstructor.Task)
  (j : Prosa.Implementation.Definitions.JobConstructor.Job) (t : Prosa.Behavior.Time.instant),
  decide
        (j ∈
          Prosa.Behavior.Arrival_sequence.arrivals_at
            (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence
              Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at ts)
            t) =
      true →
    j.job_arrival = t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_JobConstructor_job_arrival_consistent
     : forall (ts : List_inst1 Prosa_Implementation_Definitions_JobConstructor_Task)
         (j : Prosa_Implementation_Definitions_JobConstructor_Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem_inst3 Prosa_Implementation_Definitions_JobConstructor_Job
               (List_inst1 Prosa_Implementation_Definitions_JobConstructor_Job)
               (List_instMembership_inst1 Prosa_Implementation_Definitions_JobConstructor_Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_at_inst1
                  Prosa_Implementation_Definitions_JobConstructor_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
                  (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence_inst3
                     Prosa_Implementation_Definitions_Task_concrete_task
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                     Prosa_Implementation_Definitions_JobConstructor_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
                     Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
                     Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at ts)
                  t)
               j)
            (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
               (instBEqOfDecidableEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
               (instLawfulBEq_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_at_inst1
                  Prosa_Implementation_Definitions_JobConstructor_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
                  (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence_inst3
                     Prosa_Implementation_Definitions_Task_concrete_task
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                     Prosa_Implementation_Definitions_JobConstructor_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
                     Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
                     Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at ts)
                  t)))
         Bool_true ->
       @eq Prosa_Behavior_Time_instant (Prosa_Implementation_Definitions_Task_concrete_job_job_arrival j) t
```
