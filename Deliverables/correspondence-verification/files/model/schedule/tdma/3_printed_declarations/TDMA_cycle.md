# `TDMA_cycle`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.TDMA_cycle`
- Lean: `Prosa.Model.Schedule.Tdma.TDMA_cycle`
- Certificate: `TDMA_cycle_correspondence`

## Official Rocq

```coq
TDMA_cycle : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> nat

TDMA_cycle is not universe polymorphic
Arguments TDMA_cycle {Task} ts {H}
TDMA_cycle is transparent
Expands to: Constant prosa.model.schedule.tdma.TDMA_cycle
Declared in library prosa.model.schedule.tdma, line 93, characters 13-23
@TDMA_cycle
     : forall Task : eqType, {setEquality.sort Task} -> TDMAPolicy Task -> nat
```

Body:

```coq
TDMA_cycle =
fun (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task) =>
\sum_(tsk <- @_set_seq Task ts) @task_time_slot Task H tsk
     : forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> nat

Arguments TDMA_cycle {Task} ts {H}
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.TDMA_cycle : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → ℕ
def Prosa.Model.Schedule.Tdma.TDMA_cycle.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] ts =>
  List.foldr (fun tsk n => Prosa.Model.Schedule.Tdma.task_time_slot tsk + n) 0 ts.val
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_TDMA_cycle
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> Nat
```

Body:

```coq
Prosa_Model_Schedule_Tdma_TDMA_cycle@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                      inst_3)
  (ts : Prosa_Util_Seqset_set Task inst_3) =>
List_foldr_inst2 Task Nat
  (fun (tsk : Task) (n : Nat) =>
   HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
     (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
        inst_3
        inst_6 tsk)
     n)
  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (Prosa_Util_Seqset_set_val Task inst_3 ts)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 -> Nat

Arguments Prosa_Model_Schedule_Tdma_TDMA_cycle Task
  inst_3
  inst_6 ts
```
