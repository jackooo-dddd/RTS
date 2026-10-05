# `rta_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ovh.edf.fully_nonpreemptive.rta_recurrence_solution`
- Lean: `Prosa.Results.Rta.Ovh.Edf.FullyNonpreemptive.rta_recurrence_solution`
- Certificate: `rta_recurrence_solution_correspondence`

## Official Rocq

```coq
rta_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
MaxArrivals Task ->
seq (Equality.sort Task) -> Equality.sort Task -> duration -> duration -> duration -> duration -> nat -> Prop

rta_recurrence_solution is not universe polymorphic
Arguments rta_recurrence_solution {Task H H0 H1} ts%seq_scope tsk DB CSB CRPDB L R%nat_scope
rta_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.ovh.edf.fully_nonpreemptive.rta_recurrence_solution
Declared in library prosa.results.rta.ovh.edf.fully_nonpreemptive, line 166, characters 13-36
@rta_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> duration -> duration -> duration -> duration -> nat -> Prop
```

Body:

```coq
rta_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (DB CSB CRPDB : duration) =>
let overhead_bound :=
  fun Δ : duration => (DB + CSB + CRPDB) * (1 + 2 * (\sum_(tsk_o <- ts) @max_arrivals Task H1 tsk_o Δ)) in
fun (L : duration) (R : nat) =>
forall A : duration,
is_true (@is_in_search_space Task H H0 (@fully_nonpreemptive_task_model Task H) ts H1 tsk L A) ->
exists F : duration,
  is_true
    (overhead_bound F + @blocking_bound Task H H0 (@fully_nonpreemptive_task_model Task H) ts H1 tsk A +
     (@task_request_bound_function Task H H1 tsk (A + 1) - (@task_cost Task H tsk - 1)) +
     @bound_on_athep_workload Task H H0 H1 ts tsk A F <= F) /\
  is_true (F + (overhead_bound (A + R) - overhead_bound F) + (@task_cost Task H tsk - 1) <= A + R)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> duration -> duration -> duration -> duration -> nat -> Prop

Arguments rta_recurrence_solution {Task H H0 H1} ts%seq_scope tsk DB CSB CRPDB L R%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Ovh.Edf.FullyNonpreemptive.rta_recurrence_solution : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          List Task →
            Task →
              Prosa.Behavior.Time.duration →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ → Prop
```

Body:

```lean
def Prosa.Results.Rta.Ovh.Edf.FullyNonpreemptive.rta_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          List Task →
            Task →
              Prosa.Behavior.Time.duration →
                Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts tsk DB CSB CRPDB L R =>
  have overhead_bound := fun Δ =>
    (DB + CSB + CRPDB) *
      (1 + 2 * Prosa.Util.Sum.sumSeq ts fun tsk_o => Prosa.Model.Task.Arrival.Curves.max_arrivals tsk_o Δ);
  ∀ (A : Prosa.Behavior.Time.duration),
    Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf.is_in_search_space ts tsk L A = true →
      ∃ F,
        overhead_bound F + Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk A +
                (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                  (Prosa.Model.Task.Concept.task_cost tsk - 1)) +
              Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk A F ≤
            F ∧
          F + (overhead_bound (A + R) - overhead_bound F) + (Prosa.Model.Task.Concept.task_cost tsk - 1) ≤ A + R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ovh_Edf_FullyNonpreemptive_rta_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat -> SProp
```

Body:

```coq
Prosa_Results_Rta_Ovh_Edf_FullyNonpreemptive_rta_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Concept_TaskDeadline Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (tsk : Task) (DB CSB CRPDB L : Prosa_Behavior_Time_duration) (R : Nat) =>
let overhead_bound :=
  fun _UU0394_ : Prosa_Behavior_Time_duration =>
  HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
       (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
          Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) DB CSB)
       CRPDB)
    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
       (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))
       (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
          (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
          (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 2 (instOfNatNat 2))
          (Prosa_Util_Sum_sumSeq Task ts
             (fun tsk_o : Task =>
              Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                inst_3
                inst_12 tsk_o
                _UU0394_))))
  in
forall A : Prosa_Behavior_Time_duration,
@eq Bool
  (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Edf_is_in_search_space Task
     inst_3
     inst_6
     inst_9
     (Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task
        inst_3
        inst_6)
     ts inst_12 tsk L A)
  Bool_true ->
Exists Prosa_Behavior_Time_duration
  (fun F : Prosa_Behavior_Time_duration =>
   And
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
              (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
              (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                 (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (overhead_bound F)
                 (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                    inst_3
                    inst_6
                    inst_9
                    (Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task
                       inst_3
                       inst_6)
                    ts inst_12 tsk
                    A))
              (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                 (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                    inst_3
                    inst_6
                    inst_12 tsk
                    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                       Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                       A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                 (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                    (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                       inst_3
                       inst_6 tsk)
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
           (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
              inst_3
              inst_6
              inst_9
              inst_12 ts tsk A F))
        F)
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
           Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) F
              (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                 (overhead_bound
                    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                       (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R))
                 (overhead_bound F)))
           (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
              (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                 inst_3
                 inst_6 tsk)
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat -> SProp

Arguments Prosa_Results_Rta_Ovh_Edf_FullyNonpreemptive_rta_recurrence_solution Task
  inst_3
  inst_6
  inst_9
  inst_12 
  ts tsk DB CSB CRPDB L
  x____at___Init_Prelude3715277255__hygCtx13_Init_Prelude3715277255__hygCtx__hyg24%_Nat_scope
```
