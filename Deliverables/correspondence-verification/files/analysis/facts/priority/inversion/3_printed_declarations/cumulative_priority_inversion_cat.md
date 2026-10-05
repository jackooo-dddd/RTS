# `cumulative_priority_inversion_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.inversion.cumulative_priority_inversion_cat`
- Lean: `Prosa.Analysis.Facts.Priority.Inversion.cumulative_priority_inversion_cat`
- Certificate: `cumulative_priority_inversion_cat_correspondence`

## Official Rocq

```coq
cumulative_priority_inversion_cat :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {JLFP : JLFP_policy Job} (j : Equality.sort Job) 
  (t_mid t1 t2 : instant),
is_true (t1 <= t_mid) ->
is_true (t_mid <= t2) ->
@cumulative_priority_inversion Job PState arr_seq sched JLFP j t1 t2 =
@cumulative_priority_inversion Job PState arr_seq sched JLFP j t1 t_mid +
@cumulative_priority_inversion Job PState arr_seq sched JLFP j t_mid t2

cumulative_priority_inversion_cat is not universe polymorphic
Arguments cumulative_priority_inversion_cat {Job PState} arr_seq sched {JLFP} j t_mid t1 t2 _ _
cumulative_priority_inversion_cat is opaque
Expands to: Constant prosa.analysis.facts.priority.inversion.cumulative_priority_inversion_cat
Declared in library prosa.analysis.facts.priority.inversion, line 144, characters 8-41
@cumulative_priority_inversion_cat
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLFP : JLFP_policy Job) (j : Equality.sort Job)
         (t_mid t1 t2 : instant),
       is_true (t1 <= t_mid) ->
       is_true (t_mid <= t2) ->
       @cumulative_priority_inversion Job PState arr_seq sched JLFP j t1 t2 =
       @cumulative_priority_inversion Job PState arr_seq sched JLFP j t1 t_mid +
       @cumulative_priority_inversion Job PState arr_seq sched JLFP j t_mid t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Inversion.cumulative_priority_inversion_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j : Job) (t_mid t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t_mid →
    t_mid ≤ t2 →
      Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion arr_seq sched j t1 t2 =
        Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion arr_seq sched j t1 t_mid +
          Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion arr_seq sched j t_mid t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Inversion_cumulative_priority_inversion_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job) (t_mid t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t_mid ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t_mid t2 ->
       @eq Nat
         (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion Job
            inst_3 PState arr_seq sched
            JLFP j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion Job
               inst_3 PState arr_seq
               sched JLFP j t1 t_mid)
            (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion Job
               inst_3 PState arr_seq
               sched JLFP j t_mid t2))
```
