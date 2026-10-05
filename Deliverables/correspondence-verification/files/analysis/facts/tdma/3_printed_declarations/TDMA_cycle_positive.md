# `TDMA_cycle_positive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.tdma.TDMA_cycle_positive`
- Lean: `Prosa.Analysis.Facts.Tdma.TDMA_cycle_positive`
- Certificate: `TDMA_cycle_positive_correspondence`

## Official Rocq

```coq
TDMA_cycle_positive :
forall {Task : eqType} (ts : {setEquality.sort Task}) {H : TDMAPolicy Task} (task : Equality.sort Task),
is_true (task \in ts) -> @valid_time_slot Task ts H -> is_true (0 < @TDMA_cycle Task ts H)

TDMA_cycle_positive is not universe polymorphic
Arguments TDMA_cycle_positive {Task} ts {H} task H_task_in_ts time_slot_positive
TDMA_cycle_positive is opaque
Expands to: Constant prosa.analysis.facts.tdma.TDMA_cycle_positive
Declared in library prosa.analysis.facts.tdma, line 34, characters 10-29
@TDMA_cycle_positive
     : forall (Task : eqType) (ts : {setEquality.sort Task}) (H : TDMAPolicy Task)
         (task : Equality.sort Task),
       is_true (task \in ts) -> @valid_time_slot Task ts H -> is_true (0 < @TDMA_cycle Task ts H)
```

## Lean

```lean
@Prosa.Analysis.Facts.Tdma.TDMA_cycle_positive : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  (ts : Prosa.Util.Seqset.set Task) [inst_1 : Prosa.Model.Schedule.Tdma.TDMAPolicy Task],
  ∀ task ∈ ts, Prosa.Model.Schedule.Tdma.valid_time_slot ts → 0 < Prosa.Model.Schedule.Tdma.TDMA_cycle ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Tdma_TDMA_cycle_positive
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
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Schedule_Tdma_TDMA_cycle Task
            inst_3
            inst_9 ts)
```
