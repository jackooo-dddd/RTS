# `task_in_time_slot`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.task_in_time_slot`
- Lean: `Prosa.Model.Schedule.Tdma.task_in_time_slot`
- Certificate: `task_in_time_slot_correspondence`

## Official Rocq

```coq
task_in_time_slot :
forall {Task : eqType}, {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Task -> instant -> bool

task_in_time_slot is not universe polymorphic
Arguments task_in_time_slot {Task} ts {H} tsk t
task_in_time_slot is transparent
Expands to: Constant prosa.model.schedule.tdma.task_in_time_slot
Declared in library prosa.model.schedule.tdma, line 104, characters 13-30
@task_in_time_slot
     : forall Task : eqType,
       {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Task -> instant -> bool
```

Body:

```coq
task_in_time_slot =
fun (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task) (tsk : Equality.sort Task)
  (t : instant) =>
(t + @TDMA_cycle Task ts H - @task_slot_offset Task ts H tsk %% @TDMA_cycle Task ts H)
%% @TDMA_cycle Task ts H < @task_time_slot Task H tsk
     : forall {Task : eqType},
       {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Task -> instant -> bool

Arguments task_in_time_slot {Task} ts {H} tsk t
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.task_in_time_slot : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] → Prosa.Util.Seqset.set Task → Task → Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Schedule.Tdma.task_in_time_slot.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] →
      Prosa.Util.Seqset.set Task → Task → Prosa.Behavior.Time.instant → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] ts tsk t =>
  decide
    ((t + Prosa.Model.Schedule.Tdma.TDMA_cycle ts -
          Prosa.Model.Schedule.Tdma.task_slot_offset ts tsk % Prosa.Model.Schedule.Tdma.TDMA_cycle ts) %
        Prosa.Model.Schedule.Tdma.TDMA_cycle ts <
      Prosa.Model.Schedule.Tdma.task_time_slot tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_task_in_time_slot
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Schedule_Tdma_task_in_time_slot@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                      inst_3)
  (ts : Prosa_Util_Seqset_set Task inst_3)
  (tsk : Task) (t : Prosa_Behavior_Time_instant) =>
Decidable_decide
  (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
     (HMod_hMod_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
        (instHMod_inst1 Prosa_Behavior_Time_instant Nat_instMod)
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
              (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
              (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
                 inst_3
                 inst_6 ts))
           (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod)
              (Prosa_Model_Schedule_Tdma_task_slot_offset Task
                 inst_3
                 inst_6 ts tsk)
              (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
                 inst_3
                 inst_6 ts)))
        (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
           inst_3
           inst_6 ts))
     (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
        inst_3
        inst_6 tsk))
  (Nat_decLt
     (HMod_hMod_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
        (instHMod_inst1 Prosa_Behavior_Time_instant Nat_instMod)
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
              (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
              (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
                 inst_3
                 inst_6 ts))
           (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod)
              (Prosa_Model_Schedule_Tdma_task_slot_offset Task
                 inst_3
                 inst_6 ts tsk)
              (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
                 inst_3
                 inst_6 ts)))
        (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
           inst_3
           inst_6 ts))
     (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
        inst_3
        inst_6 tsk))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Schedule_Tdma_task_in_time_slot Task
  inst_3
  inst_6 ts tsk t
```
