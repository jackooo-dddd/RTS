# `task_slot_offset`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.task_slot_offset`
- Lean: `Prosa.Model.Schedule.Tdma.task_slot_offset`
- Certificate: `task_slot_offset_correspondence`

## Official Rocq

```coq
task_slot_offset :
forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Task -> nat

task_slot_offset is not universe polymorphic
Arguments task_slot_offset {Task} ts {H} tsk
task_slot_offset is transparent
Expands to: Constant prosa.model.schedule.tdma.task_slot_offset
Declared in library prosa.model.schedule.tdma, line 99, characters 13-29
@task_slot_offset
     : forall Task : eqType, {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Task -> nat
```

Body:

```coq
task_slot_offset =
fun (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task) (tsk : Equality.sort Task) =>
\sum_(prev_task <- @_set_seq Task ts | @slot_order Task H prev_task tsk && (prev_task != tsk))
   @task_time_slot Task H prev_task
     : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Task -> nat

Arguments task_slot_offset {Task} ts {H} tsk
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.task_slot_offset : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Task → ℕ
def Prosa.Model.Schedule.Tdma.task_slot_offset.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Task → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] ts tsk =>
  List.foldr (fun prevTask n => Prosa.Model.Schedule.Tdma.task_time_slot prevTask + n) 0
    (List.filter (fun prevTask => Prosa.Model.Schedule.Tdma.slot_order prevTask tsk && decide (prevTask ≠ tsk)) ts.val)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_task_slot_offset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Task -> Nat
```

Body:

```coq
Prosa_Model_Schedule_Tdma_task_slot_offset@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                      inst_3)
  (ts : Prosa_Util_Seqset_set Task inst_3)
  (tsk : Task) =>
List_foldr_inst2 Task Nat
  (fun (prevTask : Task) (n : Nat) =>
   HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
     (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
        inst_3
        inst_6 prevTask)
     n)
  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (List_filter Task
     (fun prevTask : Task =>
      Bool_and
        (Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order Task
           inst_3
           inst_6 prevTask tsk)
        (Decidable_decide (Ne Task prevTask tsk)
           (instDecidableNot (@eq Task prevTask tsk)
              (inst_3 prevTask tsk))))
     (Prosa_Util_Seqset_set_val Task inst_3 ts))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Task -> Nat

Arguments Prosa_Model_Schedule_Tdma_task_slot_offset Task
  inst_3
  inst_6 ts tsk
```
