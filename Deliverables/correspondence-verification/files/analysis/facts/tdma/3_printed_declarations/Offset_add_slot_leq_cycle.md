# `Offset_add_slot_leq_cycle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.tdma.Offset_add_slot_leq_cycle`
- Lean: `Prosa.Analysis.Facts.Tdma.Offset_add_slot_leq_cycle`
- Certificate: `Offset_add_slot_leq_cycle_correspondence`

## Official Rocq

```coq
Offset_add_slot_leq_cycle :
forall {Task : eqType} (ts : {setEquality.sort Task}) {H : TDMAPolicy Task} (task : Equality.sort Task),
is_true (task \in ts) ->
is_true (@task_slot_offset Task ts H task + @task_time_slot Task H task <= @TDMA_cycle Task ts H)

Offset_add_slot_leq_cycle is not universe polymorphic
Arguments Offset_add_slot_leq_cycle {Task} ts {H} task H_task_in_ts
Offset_add_slot_leq_cycle is opaque
Expands to: Constant prosa.analysis.facts.tdma.Offset_add_slot_leq_cycle
Declared in library prosa.analysis.facts.tdma, line 53, characters 10-35
@Offset_add_slot_leq_cycle
     : forall (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task)
         (task : Equality.sort Task),
       is_true (task \in ts) ->
       is_true (@task_slot_offset Task ts H task + @task_time_slot Task H task <= @TDMA_cycle Task ts H)
```

## Lean

```lean
@Prosa.Analysis.Facts.Tdma.Offset_add_slot_leq_cycle : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (ts : Prosa.Util.Seqset.set Task) [inst_1 : Prosa.Model.Schedule.Tdma.TDMAPolicy Task],
  ∀ task ∈ ts,
    Prosa.Model.Schedule.Tdma.task_slot_offset ts task + Prosa.Model.Schedule.Tdma.task_time_slot task ≤
      Prosa.Model.Schedule.Tdma.TDMA_cycle ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Tdma_Offset_add_slot_leq_cycle
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
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Schedule_Tdma_task_slot_offset Task
               inst_3
               inst_9 ts task)
            (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
               inst_3
               inst_9 task))
         (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
            inst_3
            inst_9 ts)
```
