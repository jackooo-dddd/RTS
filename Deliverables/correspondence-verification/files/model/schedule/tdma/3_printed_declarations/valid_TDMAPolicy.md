# `valid_TDMAPolicy`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.valid_TDMAPolicy`
- Lean: `Prosa.Model.Schedule.Tdma.valid_TDMAPolicy`
- Certificate: `valid_TDMAPolicy_correspondence`

## Official Rocq

```coq
valid_TDMAPolicy : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Prop

valid_TDMAPolicy is not universe polymorphic
Arguments valid_TDMAPolicy {Task} ts {H}
valid_TDMAPolicy is transparent
Expands to: Constant prosa.model.schedule.tdma.valid_TDMAPolicy
Declared in library prosa.model.schedule.tdma, line 72, characters 13-29
@valid_TDMAPolicy
     : forall Task : eqType, {setEquality.sort Task} -> TDMAPolicy Task -> Prop
```

Body:

```coq
valid_TDMAPolicy =
fun (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task) =>
@transitive_slot_order Task H /\
@total_slot_order Task ts H /\ @antisymmetric_slot_order Task ts H /\ @valid_time_slot Task ts H
     : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Prop

Arguments valid_TDMAPolicy {Task} ts {H}
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.valid_TDMAPolicy : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Prop
def Prosa.Model.Schedule.Tdma.valid_TDMAPolicy.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] ts =>
  Prosa.Model.Schedule.Tdma.transitive_slot_order ∧
    Prosa.Model.Schedule.Tdma.total_slot_order ts ∧
      Prosa.Model.Schedule.Tdma.antisymmetric_slot_order ts ∧ Prosa.Model.Schedule.Tdma.valid_time_slot ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_valid_TDMAPolicy
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp
```

Body:

```coq
Prosa_Model_Schedule_Tdma_valid_TDMAPolicy@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                      inst_3)
  (ts : Prosa_Util_Seqset_set Task inst_3) =>
And
  (Prosa_Model_Schedule_Tdma_transitive_slot_order Task
     inst_3
     inst_6)
  (And
     (Prosa_Model_Schedule_Tdma_total_slot_order Task
        inst_3
        inst_6 ts)
     (And
        (Prosa_Model_Schedule_Tdma_antisymmetric_slot_order Task
           inst_3
           inst_6 ts)
        (Prosa_Model_Schedule_Tdma_valid_time_slot Task
           inst_3
           inst_6 ts)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp

Arguments Prosa_Model_Schedule_Tdma_valid_TDMAPolicy Task
  inst_3
  inst_6 ts
```
