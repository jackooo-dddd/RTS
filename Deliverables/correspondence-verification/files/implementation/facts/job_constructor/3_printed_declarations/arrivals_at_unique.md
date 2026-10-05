# `arrivals_at_unique`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.job_constructor.arrivals_at_unique`
- Lean: `Prosa.Implementation.Facts.JobConstructor.arrivals_at_unique`
- Certificate: `arrivals_at_unique_correspondence`

## Official Rocq

```coq
arrivals_at_unique :
forall ts : seq (Equality.sort Task),
is_true (@uniq Task ts) ->
forall t : instant,
is_true
  (@uniq Job
     (@arrivals_at Job
        (@concrete_arrival_sequence task_concrete_task__canonical__eqtype_Equality Job ConcreteMaxArrivals
           generate_jobs_at ts)
        t))

arrivals_at_unique is not universe polymorphic
Arguments arrivals_at_unique ts%seq_scope H_ts_uniq t
arrivals_at_unique is opaque
Expands to: Constant prosa.implementation.facts.job_constructor.arrivals_at_unique
Declared in library prosa.implementation.facts.job_constructor, line 46, characters 8-26
arrivals_at_unique
     : forall ts : seq (Equality.sort Task),
       is_true (@uniq Task ts) ->
       forall t : instant,
       is_true
         (@uniq Job
            (@arrivals_at Job
               (@concrete_arrival_sequence task_concrete_task__canonical__eqtype_Equality Job
                  ConcreteMaxArrivals generate_jobs_at ts)
               t))
```

## Lean

```lean
Prosa.Implementation.Facts.JobConstructor.arrivals_at_unique : ∀
  (ts : List Prosa.Implementation.Definitions.JobConstructor.Task),
  ts.Nodup →
    ∀ (t : Prosa.Behavior.Time.instant),
      (Prosa.Behavior.Arrival_sequence.arrivals_at
          (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence
            Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at ts)
          t).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_JobConstructor_arrivals_at_unique
     : forall ts : List_inst1 Prosa_Implementation_Definitions_JobConstructor_Task,
       List_Nodup_inst1 Prosa_Implementation_Definitions_JobConstructor_Task ts ->
       forall t : Prosa_Behavior_Time_instant,
       List_Nodup_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
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
```
