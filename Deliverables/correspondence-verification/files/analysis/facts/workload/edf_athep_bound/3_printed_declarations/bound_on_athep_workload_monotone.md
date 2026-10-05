# `bound_on_athep_workload_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_monotone`
- Lean: `Prosa.Analysis.Facts.Workload.EdfAthepBound.bound_on_athep_workload_monotone`
- Certificate: `bound_on_athep_workload_monotone_correspondence`

## Official Rocq

```coq
bound_on_athep_workload_monotone :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H1 : MaxArrivals Task}
  (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H1) ->
forall (tsk : Equality.sort Task) (A : nat),
@monotone nat leq (@bound_on_athep_workload Task H H0 H1 ts tsk A)

bound_on_athep_workload_monotone is not universe polymorphic
Arguments bound_on_athep_workload_monotone {Task H H0 H1} ts%seq_scope H_valid_taskset_arrival_curve 
  tsk A%nat_scope x y _
bound_on_athep_workload_monotone is opaque
Expands to: Constant prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_monotone
Declared in library prosa.analysis.facts.workload.edf_athep_bound, line 182, characters 8-40
@bound_on_athep_workload_monotone
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
         (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H1) ->
       forall (tsk : Equality.sort Task) (A : nat),
       @monotone nat leq (@bound_on_athep_workload Task H H0 H1 ts tsk A)
```

## Lean

```lean
@Prosa.Analysis.Facts.Workload.EdfAthepBound.bound_on_athep_workload_monotone : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task) (A : ℕ),
      Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
        (Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk A)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Workload_EdfAthepBound_bound_on_athep_workload_monotone
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_12) ->
       forall (tsk : Task) (A : Nat),
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun x y : Nat => Decidable_decide (LE_le_inst1 Nat instLENat x y) (Nat_decLe x y))
         (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
            inst_3
            inst_6
            inst_9
            inst_12 ts tsk A)
```
