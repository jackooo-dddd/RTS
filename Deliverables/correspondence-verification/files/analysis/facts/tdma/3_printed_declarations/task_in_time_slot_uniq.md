# `task_in_time_slot_uniq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.tdma.task_in_time_slot_uniq`
- Lean: `Prosa.Analysis.Facts.Tdma.task_in_time_slot_uniq`
- Certificate: `task_in_time_slot_uniq_correspondence`

## Official Rocq

```coq
task_in_time_slot_uniq :
forall {Task : eqType} (ts : {setEquality.sort Task}) {H : TDMAPolicy Task} (task : Equality.sort Task),
is_true (task \in ts) ->
@valid_time_slot Task ts H ->
@total_slot_order Task ts H ->
@antisymmetric_slot_order Task ts H ->
@transitive_slot_order Task H ->
forall (tsk1 tsk2 : Equality.sort Task) (t : instant),
is_true (tsk1 \in ts) ->
is_true (0 < @task_time_slot Task H tsk1) ->
is_true (tsk2 \in ts) ->
is_true (0 < @task_time_slot Task H tsk2) ->
is_true (@task_in_time_slot Task ts H tsk1 t) -> is_true (@task_in_time_slot Task ts H tsk2 t) -> tsk1 = tsk2

task_in_time_slot_uniq is not universe polymorphic
Arguments task_in_time_slot_uniq {Task} ts {H} task H_task_in_ts time_slot_positive 
  slot_order_total slot_order_antisymmetric slot_order_transitive tsk1 tsk2 t _ _ 
  _ _ _ _
task_in_time_slot_uniq is opaque
Expands to: Constant prosa.analysis.facts.tdma.task_in_time_slot_uniq
Declared in library prosa.analysis.facts.tdma, line 120, characters 10-32
@task_in_time_slot_uniq
     : forall (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task)
         (task : Equality.sort Task),
       is_true (task \in ts) ->
       @valid_time_slot Task ts H ->
       @total_slot_order Task ts H ->
       @antisymmetric_slot_order Task ts H ->
       @transitive_slot_order Task H ->
       forall (tsk1 tsk2 : Equality.sort Task) (t : instant),
       is_true (tsk1 \in ts) ->
       is_true (0 < @task_time_slot Task H tsk1) ->
       is_true (tsk2 \in ts) ->
       is_true (0 < @task_time_slot Task H tsk2) ->
       is_true (@task_in_time_slot Task ts H tsk1 t) ->
       is_true (@task_in_time_slot Task ts H tsk2 t) -> tsk1 = tsk2
```

## Lean

```lean
@Prosa.Analysis.Facts.Tdma.task_in_time_slot_uniq : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (ts : Prosa.Util.Seqset.set Task) [inst_1 : Prosa.Model.Schedule.Tdma.TDMAPolicy Task],
  ∀ task ∈ ts,
    Prosa.Model.Schedule.Tdma.valid_time_slot ts →
      Prosa.Model.Schedule.Tdma.total_slot_order ts →
        Prosa.Model.Schedule.Tdma.antisymmetric_slot_order ts →
          Prosa.Model.Schedule.Tdma.transitive_slot_order →
            ∀ (tsk1 tsk2 : Task) (t : Prosa.Behavior.Time.instant),
              tsk1 ∈ ts →
                0 < Prosa.Model.Schedule.Tdma.task_time_slot tsk1 →
                  tsk2 ∈ ts →
                    0 < Prosa.Model.Schedule.Tdma.task_time_slot tsk2 →
                      Prosa.Model.Schedule.Tdma.task_in_time_slot ts tsk1 t = true →
                        Prosa.Model.Schedule.Tdma.task_in_time_slot ts tsk2 t = true → tsk1 = tsk2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Tdma_task_in_time_slot_uniq
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
       Prosa_Model_Schedule_Tdma_total_slot_order Task
         inst_3
         inst_9 ts ->
       Prosa_Model_Schedule_Tdma_antisymmetric_slot_order Task
         inst_3
         inst_9 ts ->
       Prosa_Model_Schedule_Tdma_transitive_slot_order Task
         inst_3
         inst_9 ->
       forall (tsk1 tsk2 : Task) (t : Prosa_Behavior_Time_instant),
       Membership_mem Task
         (Prosa_Util_Seqset_set Task inst_3)
         (Prosa_Util_Seqset_instMembershipSet Task
            inst_3)
         ts tsk1 ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
            inst_3
            inst_9 tsk1) ->
       Membership_mem Task
         (Prosa_Util_Seqset_set Task inst_3)
         (Prosa_Util_Seqset_instMembershipSet Task
            inst_3)
         ts tsk2 ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot Task
            inst_3
            inst_9 tsk2) ->
       @eq Bool
         (Prosa_Model_Schedule_Tdma_task_in_time_slot Task
            inst_3
            inst_9 ts tsk1 t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Schedule_Tdma_task_in_time_slot Task
            inst_3
            inst_9 ts tsk2 t)
         Bool_true ->
       @eq Task tsk1 tsk2
```
