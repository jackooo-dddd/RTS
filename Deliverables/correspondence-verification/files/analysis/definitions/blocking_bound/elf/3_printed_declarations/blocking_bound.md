# `blocking_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.blocking_bound.elf.blocking_bound`
- Lean: `Prosa.Analysis.Definitions.BlockingBound.Elf.blocking_bound`
- Certificate: `blocking_bound_correspondence`

## Official Rocq

```coq
blocking_bound :
forall {Task : TaskType},
TaskCost Task ->
TaskMaxNonpreemptiveSegment Task ->
gel.PriorityPoint Task ->
seq (Equality.sort Task) -> MaxArrivals Task -> FP_policy Task -> Equality.sort Task -> duration -> nat

blocking_bound is not universe polymorphic
Arguments blocking_bound {Task H H0 H1} ts%seq_scope {H2 FP} tsk A
blocking_bound is transparent
Expands to: Constant prosa.analysis.definitions.blocking_bound.elf.blocking_bound
Declared in library prosa.analysis.definitions.blocking_bound.elf, line 50, characters 13-27
@blocking_bound
     : forall Task : TaskType,
       TaskCost Task ->
       TaskMaxNonpreemptiveSegment Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) ->
       MaxArrivals Task -> FP_policy Task -> Equality.sort Task -> duration -> nat
```

Body:

```coq
blocking_bound =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskMaxNonpreemptiveSegment Task)
  (H1 : gel.PriorityPoint Task) (ts : seq (Equality.sort Task)) (H2 : MaxArrivals Task) 
  (FP : FP_policy Task) =>
let blocking_relevant :=
  fun tsk_o : Equality.sort Task => (0 < @max_arrivals Task H2 tsk_o 1) && (0 < @task_cost Task H tsk_o) in
let lp_tsk_blocking_relevant :=
  fun tsk tsk_o : Equality.sort Task => @hp_task Task FP tsk tsk_o && blocking_relevant tsk_o in
let ep_tsk_blocking_relevant :=
  fun (tsk tsk_o : Equality.sort Task) (A : duration) =>
  let ep_tsk_j_blocking_relevant :=
    @order.Order.lt ssrnum.ring_display
      (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
         ssrint.ssrint_int__canonical__Num_POrderedZmodule)
      (@ssralg.GRing.add
         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
            ssrint.ssrint_int__canonical__GRing_PzSemiRing)
         (@ssralg.GRing.natmul
            (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
               ssrint.ssrint_int__canonical__GRing_PzSemiRing)
            (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) A)
         (@gel.task_priority_point Task H1 tsk))
      (@gel.task_priority_point Task H1 tsk_o)
    in
  @ep_task Task FP tsk tsk_o && ep_tsk_j_blocking_relevant && blocking_relevant tsk_o in
fun (tsk : Equality.sort Task) (A : duration) =>
\max_(tsk_o <- ts | lp_tsk_blocking_relevant tsk tsk_o || ep_tsk_blocking_relevant tsk tsk_o A)
   (@task_max_nonpreemptive_segment Task H0 tsk_o - 1)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskMaxNonpreemptiveSegment Task ->
       gel.PriorityPoint Task ->
       seq (Equality.sort Task) ->
       MaxArrivals Task -> FP_policy Task -> Equality.sort Task -> duration -> nat

Arguments blocking_bound {Task H H0 H1} ts%seq_scope {H2 FP} tsk A
```

## Lean

```lean
@Prosa.Analysis.Definitions.BlockingBound.Elf.blocking_bound : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.BlockingBound.Elf.blocking_bound.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
    [Prosa.Model.Priority.Gel.PriorityPoint Task] ts [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
    [Prosa.Model.Priority.Definitions.FP_policy Task] tsk A =>
  Prosa.Util.Minmax.bigMaxListCond ts
    (fun tsk_o =>
      Prosa.Model.Priority.Definitions.hp_task tsk tsk_o &&
          (decide (0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk_o 1) &&
            decide (0 < Prosa.Model.Task.Concept.task_cost tsk_o)) ||
        Prosa.Model.Priority.Definitions.ep_task tsk tsk_o &&
            decide
              (↑A + Prosa.Model.Priority.Gel.task_priority_point tsk <
                Prosa.Model.Priority.Gel.task_priority_point tsk_o) &&
          (decide (0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk_o 1) &&
            decide (0 < Prosa.Model.Task.Concept.task_cost tsk_o)))
    fun tsk_o => Prosa.Model.Task.Preemption.Parameters.task_max_nonpreemptive_segment tsk_o - 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BlockingBound_Elf_blocking_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_BlockingBound_Elf_blocking_bound@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (ts : List Task)
  (inst_17 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (tsk : Task) (A : Prosa_Behavior_Time_duration) =>
Prosa_Util_Minmax_bigMaxListCond Task ts
  (fun tsk_o : Task =>
   Bool_or
     (Bool_and
        (Prosa_Model_Priority_Definitions_hp_task Task
           inst_3 FP tsk tsk_o)
        (Bool_and
           (Decidable_decide
              (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                    inst_3
                    inst_17 tsk_o
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
              (Nat_decLt (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                    inst_3
                    inst_17 tsk_o
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
           (Decidable_decide
              (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                    inst_3
                    inst_6 tsk_o))
              (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                    inst_3
                    inst_6 tsk_o)))))
     (Bool_and
        (Bool_and
           (Prosa_Model_Priority_Definitions_ep_task Task
              inst_3 FP tsk tsk_o)
           (Decidable_decide
              (LT_lt_inst1 Int Int_instLTInt
                 (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                    (Nat_cast_inst1 Int instNatCastInt A)
                    (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                       inst_3
                       inst_12 tsk))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_12 tsk_o))
              (Int_decLt
                 (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                    (Nat_cast_inst1 Int instNatCastInt A)
                    (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                       inst_3
                       inst_12 tsk))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_12 tsk_o))))
        (Bool_and
           (Decidable_decide
              (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                    inst_3
                    inst_17 tsk_o
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
              (Nat_decLt (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                    inst_3
                    inst_17 tsk_o
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
           (Decidable_decide
              (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                    inst_3
                    inst_6 tsk_o))
              (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                 (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                    inst_3
                    inst_6 tsk_o))))))
  (fun tsk_o : Task =>
   HSub_hSub_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
     (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
     (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment Task
        inst_3
        inst_9 tsk_o)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_BlockingBound_Elf_blocking_bound Task
  inst_3
  inst_6
  inst_9
  inst_12 
  ts inst_17 
  FP tsk a____at____internal__hyg0
```
