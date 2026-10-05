# `hep_rbf_taskwise_partitioning`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.hep_rbf_taskwise_partitioning`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.hep_rbf_taskwise_partitioning`
- Certificate: `hep_rbf_taskwise_partitioning_correspondence`

## Official Rocq

```coq
hep_rbf_taskwise_partitioning :
forall {Task : TaskType} {H : TaskCost Task} {H2 : MaxArrivals Task} {FP : FP_policy Task}
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (L : duration),
@total_hep_request_bound_function_FP Task H H2 ts FP tsk L =
@total_hp_request_bound_function_FP Task H H2 ts FP tsk L +
@total_ep_request_bound_function_FP Task H H2 ts FP tsk L

hep_rbf_taskwise_partitioning is not universe polymorphic
Arguments hep_rbf_taskwise_partitioning {Task H H2 FP} ts%seq_scope tsk L
hep_rbf_taskwise_partitioning is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.hep_rbf_taskwise_partitioning
Declared in library prosa.analysis.facts.model.rbf, line 522, characters 8-37
@hep_rbf_taskwise_partitioning
     : forall (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (FP : FP_policy Task)
         (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (L : duration),
       @total_hep_request_bound_function_FP Task H H2 ts FP tsk L =
       @total_hp_request_bound_function_FP Task H H2 ts FP tsk L +
       @total_ep_request_bound_function_FP Task H H2 ts FP tsk L
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.hep_rbf_taskwise_partitioning : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (FP : Prosa.Model.Priority.Definitions.FP_policy Task)
  (ts : List Task) (tsk : Task) (L : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk L =
    Prosa.Analysis.Definitions.RequestBoundFunction.total_hp_request_bound_function_FP ts tsk L +
      Prosa.Analysis.Definitions.RequestBoundFunction.total_ep_request_bound_function_FP ts tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_hep_rbf_taskwise_partitioning
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (ts : List Task) (tsk : Task) (L : Prosa_Behavior_Time_duration),
       @eq Nat
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
            inst_3
            inst_6
            inst_9 ts FP tsk L)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP Task
               inst_3
               inst_6
               inst_9 ts FP tsk L)
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_ep_request_bound_function_FP Task
               inst_3
               inst_6
               inst_9 ts FP tsk L))
```
