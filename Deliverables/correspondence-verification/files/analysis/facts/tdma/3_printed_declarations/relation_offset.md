# `relation_offset`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.tdma.relation_offset`
- Lean: `Prosa.Analysis.Facts.Tdma.relation_offset`
- Certificate: `relation_offset_correspondence`

## Official Rocq

```coq
relation_offset :
forall {Task : eqType} (ts : {setEquality.sort Task}) {H : TDMAPolicy Task},
@antisymmetric_slot_order Task ts H ->
@transitive_slot_order Task H ->
forall tsk1 tsk2 : Equality.sort Task,
is_true (tsk1 \in ts) ->
is_true (tsk2 \in ts) ->
is_true (@slot_order Task H tsk1 tsk2) ->
is_true (tsk1 != tsk2) ->
is_true (@task_slot_offset Task ts H tsk1 + @task_time_slot Task H tsk1 <= @task_slot_offset Task ts H tsk2)

relation_offset is not universe polymorphic
Arguments relation_offset {Task} ts {H} slot_order_antisymmetric slot_order_transitive tsk1 tsk2 _ _ _ _
relation_offset is opaque
Expands to: Constant prosa.analysis.facts.tdma.relation_offset
Declared in library prosa.analysis.facts.tdma, line 90, characters 10-25
@relation_offset
     : forall (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task),
       @antisymmetric_slot_order Task ts H ->
       @transitive_slot_order Task H ->
       forall tsk1 tsk2 : Equality.sort Task,
       is_true (tsk1 \in ts) ->
       is_true (tsk2 \in ts) ->
       is_true (@slot_order Task H tsk1 tsk2) ->
       is_true (tsk1 != tsk2) ->
       is_true
         (@task_slot_offset Task ts H tsk1 + @task_time_slot Task H tsk1 <= @task_slot_offset Task ts H tsk2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Tdma.relation_offset : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  (ts : Prosa.Util.Seqset.set Task) [inst_1 : Prosa.Model.Schedule.Tdma.TDMAPolicy Task],
  Prosa.Model.Schedule.Tdma.antisymmetric_slot_order ts →
    Prosa.Model.Schedule.Tdma.transitive_slot_order →
      ∀ (tsk1 tsk2 : Task),
        tsk1 ∈ ts →
          tsk2 ∈ ts →
            Prosa.Model.Schedule.Tdma.slot_order tsk1 tsk2 = true →
              decide (tsk1 ≠ tsk2) = true →
                Prosa.Model.Schedule.Tdma.task_slot_offset ts tsk1 + Prosa.Model.Schedule.Tdma.task_time_slot tsk1 ≤
                  Prosa.Model.Schedule.Tdma.task_slot_offset ts tsk2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Tdma_relation_offset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (ts : Prosa_Util_Seqset_set Task inst_3)
         (inst_9 : Prosa_Model_Schedule_Tdma_TDMAPolicy
                                                                             Task
                                                                             inst_3),
       Prosa_Model_Schedule_Tdma_antisymmetric_slot_order Task
         inst_3
         inst_9 ts ->
       Prosa_Model_Schedule_Tdma_transitive_slot_order Task
         inst_3
         inst_9 ->
       forall tsk1 tsk2 : Task,
       Membership_mem Task
         (Prosa_Util_Seqset_set Task inst_3)
         (Prosa_Util_Seqset_instMembershipSet Task
            inst_3)
         ts tsk1 ->
       Membership_mem Task
         (Prosa_Util_Seqset_set Task inst_3)
         (Prosa_Util_Seqset_instMembershipSet Task
            inst_3)
         ts tsk2 ->
       @eq Bool
         (Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order Task
            inst_3
            inst_9 tsk1 tsk2)
         Bool_true ->
       @eq Bool
         (Decidable_decide (Ne Task tsk1 tsk2)
            (instDecidableNot (@eq Task tsk1 tsk2)
               (inst_3 tsk1 tsk2)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Schedule_Tdma_task_slot_offset Task
               inst_3
               inst_9 ts tsk1)
            (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
               inst_3
               inst_9 tsk1))
         (Prosa_Model_Schedule_Tdma_task_slot_offset Task
            inst_3
            inst_9 ts tsk2)
```
