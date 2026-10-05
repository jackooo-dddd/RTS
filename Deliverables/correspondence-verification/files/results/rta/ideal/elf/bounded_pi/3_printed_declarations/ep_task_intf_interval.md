# `ep_task_intf_interval`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.ep_task_intf_interval`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval`
- Certificate: `ep_task_intf_interval_correspondence`

## Official Rocq

```coq
ep_task_intf_interval :
forall {Task : TaskType},
PriorityPoint Task ->
Equality.sort Task ->
Equality.sort Task ->
instant -> GRing.Nmodule.sort (GRing_PzSemiRing__to__GRing_Nmodule ssrint_int__canonical__GRing_PzSemiRing)

ep_task_intf_interval is not universe polymorphic
Arguments ep_task_intf_interval {Task H3} tsk tsk_o A
ep_task_intf_interval is transparent
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.ep_task_intf_interval
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 316, characters 13-34
@ep_task_intf_interval
     : forall Task : TaskType,
       PriorityPoint Task ->
       Equality.sort Task ->
       Equality.sort Task ->
       instant ->
       GRing.Nmodule.sort (GRing_PzSemiRing__to__GRing_Nmodule ssrint_int__canonical__GRing_PzSemiRing)
```

Body:

```coq
ep_task_intf_interval =
fun (Task : TaskType) (H3 : PriorityPoint Task) (tsk tsk_o : Equality.sort Task) (A : instant) =>
((A + 1)%:R + @task_priority_point Task H3 tsk - @task_priority_point Task H3 tsk_o)%R
     : forall {Task : TaskType},
       PriorityPoint Task ->
       Equality.sort Task ->
       Equality.sort Task ->
       instant ->
       GRing.Nmodule.sort (GRing_PzSemiRing__to__GRing_Nmodule ssrint_int__canonical__GRing_PzSemiRing)

Arguments ep_task_intf_interval {Task H3} tsk tsk_o A
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] → Task → Task → Prosa.Behavior.Time.instant → ℤ
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] → Task → Task → Prosa.Behavior.Time.instant → ℤ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] tsk tsk_o A =>
  ↑(A + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk - Prosa.Model.Priority.Gel.task_priority_point tsk_o
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Task -> Task -> Prosa_Behavior_Time_instant -> Int
```

Body:

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (tsk tsk_o : Task) (A : Prosa_Behavior_Time_instant) =>
HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
  (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
     (Nat_cast_inst1 Int instNatCastInt
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) A
           (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
        inst_3
        inst_10 tsk))
  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
     inst_3
     inst_10 tsk_o)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Task -> Task -> Prosa_Behavior_Time_instant -> Int

Arguments Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
  inst_3
  inst_10 tsk 
  tsk_o A
```
