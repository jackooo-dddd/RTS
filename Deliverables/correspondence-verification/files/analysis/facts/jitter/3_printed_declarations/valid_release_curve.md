# `valid_release_curve`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.jitter.valid_release_curve`
- Lean: `Prosa.Analysis.Facts.Jitter.valid_release_curve`
- Certificate: `valid_release_curve_correspondence`

## Official Rocq

```coq
valid_release_curve :
forall {Task : TaskType} {arrival_curve : MaxArrivals Task} {H0 : TaskJitter Task}
  (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task arrival_curve) ->
@valid_taskset_arrival_curve Task ts (@release_curve Task arrival_curve H0)

valid_release_curve is not universe polymorphic
Arguments valid_release_curve {Task arrival_curve H0} ts%seq_scope _ tsk _
valid_release_curve is opaque
Expands to: Constant prosa.analysis.facts.jitter.valid_release_curve
Declared in library prosa.analysis.facts.jitter, line 67, characters 12-31
@valid_release_curve
     : forall (Task : TaskType) (arrival_curve : MaxArrivals Task) (H0 : TaskJitter Task)
         (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task arrival_curve) ->
       @valid_taskset_arrival_curve Task ts (@release_curve Task arrival_curve H0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Jitter.valid_release_curve : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (arrival_curve : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task)
  [inst_1 : Prosa.Model.Task.Jitter.TaskJitter Task] (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Jitter_valid_release_curve
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (arrival_curve : Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
                            inst_3)
         (inst_12 : Prosa_Model_Task_Jitter_TaskJitter
                                                                               Task
                                                                               inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3 arrival_curve) ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            (Prosa_Analysis_Facts_Jitter_release_curve Task
               inst_3 arrival_curve
               inst_12))
```
