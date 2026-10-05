# `total_slot_order`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.total_slot_order`
- Lean: `Prosa.Model.Schedule.Tdma.total_slot_order`
- Certificate: `total_slot_order_correspondence`

## Official Rocq

```coq
total_slot_order : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Prop

total_slot_order is not universe polymorphic
Arguments total_slot_order {Task} ts {H}
total_slot_order is transparent
Expands to: Constant prosa.model.schedule.tdma.total_slot_order
Declared in library prosa.model.schedule.tdma, line 60, characters 13-29
@total_slot_order
     : forall Task : eqType, {setEquality.sort Task} -> TDMAPolicy Task -> Prop
```

Body:

```coq
total_slot_order =
fun (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task) =>
@total_over_list Task (@slot_order Task H) (@_set_seq Task ts)
     : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Prop

Arguments total_slot_order {Task} ts {H}
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.total_slot_order : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Prop
def Prosa.Model.Schedule.Tdma.total_slot_order.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] ts =>
  Prosa.Util.Rel.total_over_list Prosa.Model.Schedule.Tdma.slot_order ts.val
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_total_slot_order
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp
```

Body:

```coq
Prosa_Model_Schedule_Tdma_total_slot_order@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                     inst_3)
  (ts : Prosa_Util_Seqset_set Task inst_3) =>
Prosa_Util_Rel_total_over_list Task inst_3
  (Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order Task
     inst_3
     inst_6)
  (Prosa_Util_Seqset_set_val Task inst_3 ts)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp

Arguments Prosa_Model_Schedule_Tdma_total_slot_order Task
  inst_3
  inst_6 ts
```
