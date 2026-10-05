# `valid_time_slot`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.valid_time_slot`
- Lean: `Prosa.Model.Schedule.Tdma.valid_time_slot`
- Certificate: `valid_time_slot_correspondence`

## Official Rocq

```coq
valid_time_slot : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Prop

valid_time_slot is not universe polymorphic
Arguments valid_time_slot {Task} ts {H}
valid_time_slot is transparent
Expands to: Constant prosa.model.schedule.tdma.valid_time_slot
Declared in library prosa.model.schedule.tdma, line 68, characters 13-28
@valid_time_slot
     : forall Task : eqType, {setEquality.sort Task} -> TDMAPolicy Task -> Prop
```

Body:

```coq
valid_time_slot =
fun (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task) =>
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> is_true (0 < @task_time_slot Task H tsk)
     : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Prop

Arguments valid_time_slot {Task} ts {H}
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.valid_time_slot : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Prop
def Prosa.Model.Schedule.Tdma.valid_time_slot.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] ts =>
  ∀ tsk ∈ ts, 0 < Prosa.Model.Schedule.Tdma.task_time_slot tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_valid_time_slot
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp
```

Body:

```coq
Prosa_Model_Schedule_Tdma_valid_time_slot@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                     inst_3)
  (ts : Prosa_Util_Seqset_set Task inst_3) =>
forall tsk : Task,
Membership_mem Task
  (Prosa_Util_Seqset_set Task inst_3)
  (Prosa_Util_Seqset_instMembershipSet Task inst_3) ts
  tsk ->
LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
  (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
  (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
     inst_3
     inst_6 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp

Arguments Prosa_Model_Schedule_Tdma_valid_time_slot Task
  inst_3
  inst_6 ts
```
