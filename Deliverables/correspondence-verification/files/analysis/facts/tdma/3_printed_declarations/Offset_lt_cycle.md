# `Offset_lt_cycle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.tdma.Offset_lt_cycle`
- Lean: `Prosa.Analysis.Facts.Tdma.Offset_lt_cycle`
- Certificate: `Offset_lt_cycle_correspondence`

## Official Rocq

```coq
Offset_lt_cycle :
forall {Task : eqType} (ts : {setEquality.sort Task}) {H : TDMAPolicy Task} (task : Equality.sort Task),
is_true (task \in ts) ->
@valid_time_slot Task ts H -> is_true (@task_slot_offset Task ts H task < @TDMA_cycle Task ts H)

Offset_lt_cycle is not universe polymorphic
Arguments Offset_lt_cycle {Task} ts {H} task H_task_in_ts time_slot_positive
Offset_lt_cycle is opaque
Expands to: Constant prosa.analysis.facts.tdma.Offset_lt_cycle
Declared in library prosa.analysis.facts.tdma, line 41, characters 10-25
@Offset_lt_cycle
     : forall (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task)
         (task : Equality.sort Task),
       is_true (task \in ts) ->
       @valid_time_slot Task ts H -> is_true (@task_slot_offset Task ts H task < @TDMA_cycle Task ts H)
```

## Lean

```lean
@Prosa.Analysis.Facts.Tdma.Offset_lt_cycle : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  (ts : Prosa.Util.Seqset.set Task) [inst_1 : Prosa.Model.Schedule.Tdma.TDMAPolicy Task],
  ∀ task ∈ ts,
    Prosa.Model.Schedule.Tdma.valid_time_slot ts →
      Prosa.Model.Schedule.Tdma.task_slot_offset ts task < Prosa.Model.Schedule.Tdma.TDMA_cycle ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Tdma_Offset_lt_cycle
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
       Prosa_Model_Schedule_Tdma_valid_time_slot Task
         inst_3
         inst_9 ts ->
       LT_lt_inst1 Nat instLTNat
         (Prosa_Model_Schedule_Tdma_task_slot_offset Task
            inst_3
            inst_9 ts task)
         (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
            inst_3
            inst_9 ts)
```
