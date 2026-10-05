# `limited_valid_task_run_to_completion_threshold`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.limited.limited_valid_task_run_to_completion_threshold`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.limited_valid_task_run_to_completion_threshold`
- Certificate: `limited_valid_task_run_to_completion_threshold_correspondence`

## Official Rocq

```coq
limited_valid_task_run_to_completion_threshold :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskPreemptionPoints Task} {Job : JobType}
  {H1 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState),
@schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H4) arr_seq sched ->
forall ts : seq (Equality.sort Task),
@valid_fixed_preemption_points_model Task H H0 Job H1 H3 H4 arr_seq ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
is_true (0 < @task_cost Task H tsk) ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 (@limited_preemptive_job_model Job H4)
  (@limited_preemptions_rtc_threshold Task H H0) arr_seq tsk

limited_valid_task_run_to_completion_threshold is not universe polymorphic
Arguments limited_valid_task_run_to_completion_threshold {Task H H0 Job H1 H3 H4} 
  arr_seq {PState} sched H_schedule_respects_preemption_model ts%seq_scope
  H_valid_fixed_preemption_points_model tsk H_tsk_in_ts H_positive_cost
limited_valid_task_run_to_completion_threshold is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.limited.limited_valid_task_run_to_completion_threshold
Declared in library prosa.analysis.facts.preemption.rtc_threshold.limited, line 97, characters 8-54
@limited_valid_task_run_to_completion_threshold
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskPreemptionPoints Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       @schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H4) arr_seq sched ->
       forall ts : seq (Equality.sort Task),
       @valid_fixed_preemption_points_model Task H H0 Job H1 H3 H4 arr_seq ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       is_true (0 < @task_cost Task H tsk) ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 (@limited_preemptive_job_model Job H4)
         (@limited_preemptions_rtc_threshold Task H H0) arr_seq tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.limited_valid_task_run_to_completion_threshold : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  [inst_6 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq sched →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model arr_seq ts →
        ∀ (tsk : Task),
          decide (tsk ∈ ts) = true →
            0 < Prosa.Model.Task.Concept.task_cost tsk →
              Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Limited_limited_valid_task_run_to_completion_threshold
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : 
          DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
            inst_7)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_23 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState),
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model Job
         inst_3 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_3
            inst_23)
         arr_seq sched ->
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_model Task
         inst_7
         inst_10
         inst_13 Job
         inst_3
         inst_16
         inst_20
         inst_23 arr_seq
         ts ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide
            (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_7)
               (instLawfulBEq Task
                  inst_7)
               tsk ts))
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_7
            inst_10 tsk) ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_7
         inst_10 Job
         inst_3
         inst_16
         inst_20
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_3
            inst_23)
         (Prosa_Model_Task_Preemption_LimitedPreemptive_limited_preemptions_rtc_threshold Task
            inst_7
            inst_10
            inst_13)
         arr_seq tsk
```
