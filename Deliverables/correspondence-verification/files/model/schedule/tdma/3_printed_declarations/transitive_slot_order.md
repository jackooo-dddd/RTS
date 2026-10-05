# `transitive_slot_order`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.transitive_slot_order`
- Lean: `Prosa.Model.Schedule.Tdma.transitive_slot_order`
- Certificate: `transitive_slot_order_correspondence`

## Official Rocq

```coq
transitive_slot_order : forall {Task : eqType}, TDMAPolicy Task -> Prop

transitive_slot_order is not universe polymorphic
Arguments transitive_slot_order {Task H}
transitive_slot_order is transparent
Expands to: Constant prosa.model.schedule.tdma.transitive_slot_order
Declared in library prosa.model.schedule.tdma, line 57, characters 13-34
@transitive_slot_order
     : forall Task : eqType, TDMAPolicy Task -> Prop
```

Body:

```coq
transitive_slot_order =
fun (Task : eqType) (H : TDMAPolicy Task) => @transitive (Equality.sort Task) (@slot_order Task H)
     : forall {Task : eqType}, TDMAPolicy Task -> Prop

Arguments transitive_slot_order {Task H}
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.transitive_slot_order : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prop
def Prosa.Model.Schedule.Tdma.transitive_slot_order.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] =>
  ∀ (y x z : Task),
    Prosa.Model.Schedule.Tdma.slot_order x y = true →
      Prosa.Model.Schedule.Tdma.slot_order y z = true → Prosa.Model.Schedule.Tdma.slot_order x z = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_transitive_slot_order
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_Tdma_transitive_slot_order@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                      inst_3) =>
forall y x z : Task,
@eq Bool
  (Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order Task
     inst_3
     inst_6 x y)
  Bool_true ->
@eq Bool
  (Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order Task
     inst_3
     inst_6 y z)
  Bool_true ->
@eq Bool
  (Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order Task
     inst_3
     inst_6 x z)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       SProp

Arguments Prosa_Model_Schedule_Tdma_transitive_slot_order Task
  inst_3
  inst_6
```
