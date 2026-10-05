# `blackout_during_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.exceedance.SBF.blackout_during_bounded`
- Lean: `Prosa.Analysis.Facts.Model.Exceedance.SBF.blackout_during_bounded`
- Certificate: `blackout_during_bounded_correspondence`

## Official Rocq

```coq
blackout_during_bounded :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobCost Job} 
  {H2 : JobArrival Job} {H3 : JLFP_policy Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (exceedance_proc_state Job)) (e : work) (tsk : Equality.sort Task),
(forall (j : Equality.sort Job) (t1 t2 : instant),
 @arrives_in Job arr_seq j ->
 is_true (@job_of_task Job Task H0 tsk j) ->
 @busy_interval_prefix Job H2 H1 (exceedance_proc_state Job) arr_seq sched H3 j t1 t2 ->
 is_true (\sum_(t1 <= t < t2) nat_of_bool (@is_exceedance_exec Job (sched t)) <= e)) ->
forall (j : Equality.sort Job) (t1 t2 : instant) (t : nat),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
@busy_interval_prefix Job H2 H1 (exceedance_proc_state Job) arr_seq sched H3 j t1 t2 ->
is_true (t1 <= t <= t2) -> is_true (@blackout_during Job (exceedance_proc_state Job) sched t1 t <= e)

blackout_during_bounded is not universe polymorphic
Arguments blackout_during_bounded {Task Job H0 H1 H2 H3} arr_seq sched e tsk
  H_exceedance_in_busy_interval_bounded%function_scope j t1 t2 t%nat_scope _ _ _ 
  _
blackout_during_bounded is opaque
Expands to: Constant prosa.analysis.facts.model.exceedance.SBF.blackout_during_bounded
Declared in library prosa.analysis.facts.model.exceedance.SBF, line 59, characters 8-31
@blackout_during_bounded
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobCost Job)
         (H2 : JobArrival Job) (H3 : JLFP_policy Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (exceedance_proc_state Job)) (e : work) (tsk : Equality.sort Task),
       (forall (j : Equality.sort Job) (t1 t2 : instant),
        @arrives_in Job arr_seq j ->
        is_true (@job_of_task Job Task H0 tsk j) ->
        @busy_interval_prefix Job H2 H1 (exceedance_proc_state Job) arr_seq sched H3 j t1 t2 ->
        is_true (\sum_(t1 <= t < t2) nat_of_bool (@is_exceedance_exec Job (sched t)) <= e)) ->
       forall (j : Equality.sort Job) (t1 t2 : instant) (t : nat),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       @busy_interval_prefix Job H2 H1 (exceedance_proc_state Job) arr_seq sched H3 j t1 t2 ->
       is_true (t1 <= t <= t2) -> is_true (@blackout_during Job (exceedance_proc_state Job) sched t1 t <= e)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Exceedance.SBF.blackout_during_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobCost Job]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Model.Priority.Definitions.JLFP_policy Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state Job))
  (e : Prosa.Behavior.Job.work) (tsk : Task),
  (∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Task.Concept.job_of_task tsk j = true →
          Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
            ∑ t ∈ Finset.Ico t1 t2, (Prosa.Analysis.Facts.Model.IdealUniExceed.is_exceedance_exec (sched t)).toNat ≤
              e) →
    ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant) (t : ℕ),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Task.Concept.job_of_task tsk j = true →
          Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
            (decide (t1 ≤ t) && decide (t ≤ t2)) = true → Prosa.Model.Processor.Supply.blackout_during sched t1 t ≤ e
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Exceedance_SBF_blackout_during_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_20 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                       inst_7))
         (e : Prosa_Behavior_Job_work) (tsk : Task),
       (forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_7 arr_seq j ->
        @eq Bool
          (Prosa_Model_Task_Concept_job_of_task Job
             inst_7 Task
             inst_3
             inst_10 tsk j)
          Bool_true ->
        Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4 Job
          inst_7
          inst_17
          inst_14
          (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
             inst_7)
          arr_seq sched inst_20 j t1
          t2 ->
        LE_le_inst1 Nat instLENat
          (List_foldr_inst3 Nat Nat Nat_add 0
             (List_map_inst3 Nat Nat
                (fun t : Nat =>
                 Bool_toNat
                   (Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job
                      inst_7
                      (sched t)))
                (List_range' t1 (Nat_sub t2 t1) 1)))
          e) ->
       forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) (t : Nat),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4 Job
         inst_7
         inst_17
         inst_14
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_7)
         arr_seq sched inst_20 j t1
         t2 ->
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LE_le_inst1 Nat instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Processor_Supply_blackout_during_inst4 Job
            inst_7
            (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
               inst_7)
            sched t1 t)
         e
```
