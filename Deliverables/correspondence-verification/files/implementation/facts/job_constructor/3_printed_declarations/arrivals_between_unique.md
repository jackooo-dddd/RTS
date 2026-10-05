# `arrivals_between_unique`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.job_constructor.arrivals_between_unique`
- Lean: `Prosa.Implementation.Facts.JobConstructor.arrivals_between_unique`
- Certificate: `arrivals_between_unique_correspondence`

## Official Rocq

```coq
arrivals_between_unique :
forall ts : seq (Equality.sort Task),
is_true (@uniq Task ts) ->
forall t1 t2 : instant,
is_true
  (@uniq Job
     (@arrivals_between Job
        (@concrete_arrival_sequence task_concrete_task__canonical__eqtype_Equality Job ConcreteMaxArrivals
           generate_jobs_at ts)
        t1 t2))

arrivals_between_unique is not universe polymorphic
Arguments arrivals_between_unique ts%seq_scope H_ts_uniq t1 t2
arrivals_between_unique is opaque
Expands to: Constant prosa.implementation.facts.job_constructor.arrivals_between_unique
Declared in library prosa.implementation.facts.job_constructor, line 58, characters 8-31
arrivals_between_unique
     : forall ts : seq (Equality.sort Task),
       is_true (@uniq Task ts) ->
       forall t1 t2 : instant,
       is_true
         (@uniq Job
            (@arrivals_between Job
               (@concrete_arrival_sequence task_concrete_task__canonical__eqtype_Equality Job
                  ConcreteMaxArrivals generate_jobs_at ts)
               t1 t2))
```

## Lean

```lean
Prosa.Implementation.Facts.JobConstructor.arrivals_between_unique : ∀
  (ts : List Prosa.Implementation.Definitions.JobConstructor.Task),
  ts.Nodup →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      (Prosa.Behavior.Arrival_sequence.arrivals_between
          (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence
            Prosa.Implementation.Definitions.JobConstructor.generate_jobs_at ts)
          t1 t2).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_JobConstructor_arrivals_between_unique
     : forall ts : List_inst1 Prosa_Implementation_Definitions_JobConstructor_Task,
       List_Nodup_inst1 Prosa_Implementation_Definitions_JobConstructor_Task ts ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       List_Nodup_inst1 Prosa_Implementation_Definitions_JobConstructor_Job
         (Prosa_Behavior_Arrival_sequence_arrivals_between_inst1
            Prosa_Implementation_Definitions_JobConstructor_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence_inst3
               Prosa_Implementation_Definitions_Task_concrete_task
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
               Prosa_Implementation_Definitions_JobConstructor_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
               Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
               Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at ts)
            t1 t2)
```
