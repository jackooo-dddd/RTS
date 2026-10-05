# `last_segment_eq_cost_minus_rtct`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.limited.last_segment_eq_cost_minus_rtct`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.last_segment_eq_cost_minus_rtct`
- Certificate: `last_segment_eq_cost_minus_rtct_correspondence`

## Official Rocq

```coq
last_segment_eq_cost_minus_rtct :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskPreemptionPoints Task} {Job : JobType}
  {H1 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job)
  (ts : seq (Equality.sort Task)),
@valid_fixed_preemption_points_model Task H H0 Job H1 H3 H4 arr_seq ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@task_cost Task H tsk - @task_rtct Task (@limited_preemptions_rtc_threshold Task H H0) tsk =
@task_last_nonpr_segment Task H0 tsk - 1

last_segment_eq_cost_minus_rtct is not universe polymorphic
Arguments last_segment_eq_cost_minus_rtct {Task H H0 Job H1 H3 H4} arr_seq ts%seq_scope
  H_valid_fixed_preemption_points_model tsk H_tsk_in_ts
last_segment_eq_cost_minus_rtct is opaque
Expands to: Constant prosa.analysis.facts.preemption.rtc_threshold.limited.last_segment_eq_cost_minus_rtct
Declared in library prosa.analysis.facts.preemption.rtc_threshold.limited, line 144, characters 8-39
@last_segment_eq_cost_minus_rtct
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskPreemptionPoints Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)),
       @valid_fixed_preemption_points_model Task H H0 Job H1 H3 H4 arr_seq ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @task_cost Task H tsk - @task_rtct Task (@limited_preemptions_rtc_threshold Task H H0) tsk =
       @task_last_nonpr_segment Task H0 tsk - 1
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.last_segment_eq_cost_minus_rtct : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  [inst_6 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model arr_seq ts →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        Prosa.Model.Task.Concept.task_cost tsk - Prosa.Model.Task.Preemption.Parameters.task_rtct tsk =
          Prosa.Model.Task.Preemption.Parameters.task_last_nonpr_segment tsk - 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Limited_last_segment_eq_cost_minus_rtct
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
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
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
       @eq Prosa_Behavior_Time_duration
         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_7
               inst_10 tsk)
            (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
               inst_7
               (Prosa_Model_Task_Preemption_LimitedPreemptive_limited_preemptions_rtc_threshold Task
                  inst_7
                  inst_10
                  inst_13)
               tsk))
         (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment Task
               inst_7
               inst_13 tsk)
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
```
