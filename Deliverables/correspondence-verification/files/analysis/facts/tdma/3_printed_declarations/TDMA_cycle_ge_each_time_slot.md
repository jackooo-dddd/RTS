# `TDMA_cycle_ge_each_time_slot`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.tdma.TDMA_cycle_ge_each_time_slot`
- Lean: `Prosa.Analysis.Facts.Tdma.TDMA_cycle_ge_each_time_slot`
- Certificate: `TDMA_cycle_ge_each_time_slot_correspondence`

## Official Rocq

```coq
TDMA_cycle_ge_each_time_slot :
forall {Task : eqType} (ts : {setEquality.sort Task}) {H : TDMAPolicy Task} (task : Equality.sort Task),
is_true (task \in ts) -> is_true (@task_time_slot Task H task <= @TDMA_cycle Task ts H)

TDMA_cycle_ge_each_time_slot is not universe polymorphic
Arguments TDMA_cycle_ge_each_time_slot {Task} ts {H} task H_task_in_ts
TDMA_cycle_ge_each_time_slot is opaque
Expands to: Constant prosa.analysis.facts.tdma.TDMA_cycle_ge_each_time_slot
Declared in library prosa.analysis.facts.tdma, line 25, characters 10-38
@TDMA_cycle_ge_each_time_slot
     : forall (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task)
         (task : Equality.sort Task),
       is_true (task \in ts) -> is_true (@task_time_slot Task H task <= @TDMA_cycle Task ts H)
```

## Lean

```lean
@Prosa.Analysis.Facts.Tdma.TDMA_cycle_ge_each_time_slot : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (ts : Prosa.Util.Seqset.set Task) [inst_1 : Prosa.Model.Schedule.Tdma.TDMAPolicy Task],
  ∀ task ∈ ts, Prosa.Model.Schedule.Tdma.task_time_slot task ≤ Prosa.Model.Schedule.Tdma.TDMA_cycle ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Tdma_TDMA_cycle_ge_each_time_slot
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (ts : Prosa_Util_Seqset_set Task inst_3)
         (inst_9 : Prosa_Model_Schedule_Tdma_TDMAPolicy
                                                                             Task
                                                                             inst_3)
         (task : Task),
       Membership_mem Task
         (Prosa_Util_Seqset_set Task inst_3)
         (Prosa_Util_Seqset_instMembershipSet Task
            inst_3)
         ts task ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
            inst_3
            inst_9 task)
         (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
            inst_3
            inst_9 ts)
```
