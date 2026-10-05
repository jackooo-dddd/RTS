# `bound_on_total_hep_workload_changes_at`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.bound_on_total_hep_workload_changes_at`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.bound_on_total_hep_workload_changes_at`
- Certificate: `bound_on_total_hep_workload_changes_at_correspondence`

## Official Rocq

```coq
bound_on_total_hep_workload_changes_at :
forall {Task : TaskType},
gel.PriorityPoint Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat -> bool

bound_on_total_hep_workload_changes_at is not universe polymorphic
Arguments bound_on_total_hep_workload_changes_at {Task H5} ts%seq_scope tsk A%nat_scope
bound_on_total_hep_workload_changes_at is transparent
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.bound_on_total_hep_workload_changes_at
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 261, characters 13-51
@bound_on_total_hep_workload_changes_at
     : forall Task : TaskType,
       gel.PriorityPoint Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat -> bool
```

Body:

```coq
bound_on_total_hep_workload_changes_at =
fun (Task : TaskType) (H5 : gel.PriorityPoint Task) (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task) =>
let interval :=
  fun (tsk_o : Equality.sort Task) (A : instant) =>
  @ssralg.GRing.add
    (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
       ssrint.ssrint_int__canonical__GRing_PzSemiRing)
    (@ssralg.GRing.add
       (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
          ssrint.ssrint_int__canonical__GRing_PzSemiRing)
       (@ssralg.GRing.natmul
          (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
             ssrint.ssrint_int__canonical__GRing_PzSemiRing)
          (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) (A + 1))
       (@gel.task_priority_point Task H5 tsk))
    (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule (@gel.task_priority_point Task H5 tsk_o))
  in
fun A : nat =>
@has (Equality.sort Task)
  (fun tsko : Equality.sort Task => (tsk != tsko) && (interval tsko (A - 1) != interval tsko A)) ts
     : forall {Task : TaskType},
       gel.PriorityPoint Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat -> bool

Arguments bound_on_total_hep_workload_changes_at {Task H5} ts%seq_scope tsk A%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Gel.BoundedPi.bound_on_total_hep_workload_changes_at : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Priority.Gel.PriorityPoint Task] → List Task → Task → ℕ → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Gel.BoundedPi.bound_on_total_hep_workload_changes_at.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Priority.Gel.PriorityPoint Task] → List Task → Task → ℕ → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] ts tsk A =>
  ts.any fun tsko =>
    decide (tsk ≠ tsko) &&
      decide
        (↑(A - 1 + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk -
            Prosa.Model.Priority.Gel.task_priority_point tsko ≠
          ↑(A + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk -
            Prosa.Model.Priority.Gel.task_priority_point tsko)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_bound_on_total_hep_workload_changes_at
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task -> Task -> Nat -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_bound_on_total_hep_workload_changes_at@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (ts : List Task) (tsk : Task) (A : Nat) =>
List_any Task ts
  (fun tsko : Task =>
   Bool_and
     (Decidable_decide (Ne Task tsk tsko)
        (instDecidableNot (@eq Task tsk tsko)
           (inst_3 tsk tsko)))
     (Decidable_decide
        (Ne Int
           (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
              (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                 (Nat_cast_inst1 Int instNatCastInt
                    (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                       (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) A
                          (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                       (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_10 tsk))
              (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                 inst_3
                 inst_10 tsko))
           (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
              (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                 (Nat_cast_inst1 Int instNatCastInt
                    (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A
                       (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_10 tsk))
              (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                 inst_3
                 inst_10 tsko)))
        (instDecidableNot
           (@eq Int
              (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                 (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                    (Nat_cast_inst1 Int instNatCastInt
                       (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                          (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) A
                             (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                          (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                    (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                       inst_3
                       inst_10 tsk))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_10 tsko))
              (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                 (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                    (Nat_cast_inst1 Int instNatCastInt
                       (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A
                          (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                    (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                       inst_3
                       inst_10 tsk))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_10 tsko)))
           (Int_instDecidableEq
              (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                 (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                    (Nat_cast_inst1 Int instNatCastInt
                       (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                          (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) A
                             (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                          (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                    (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                       inst_3
                       inst_10 tsk))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_10 tsko))
              (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                 (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                    (Nat_cast_inst1 Int instNatCastInt
                       (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A
                          (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                    (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                       inst_3
                       inst_10 tsk))
                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                    inst_3
                    inst_10 tsko))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task -> Task -> Nat -> Bool

Arguments Prosa_Results_Rta_Ideal_Gel_BoundedPi_bound_on_total_hep_workload_changes_at 
  Task inst_3
  inst_10 ts 
  tsk x____at___Init_Prelude2408276647__hygCtx__hyg14%_Nat_scope
```
