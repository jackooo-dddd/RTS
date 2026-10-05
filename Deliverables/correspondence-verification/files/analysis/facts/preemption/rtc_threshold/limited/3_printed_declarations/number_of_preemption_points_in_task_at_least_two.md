# `number_of_preemption_points_in_task_at_least_two`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.limited.number_of_preemption_points_in_task_at_least_two`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.number_of_preemption_points_in_task_at_least_two`
- Certificate: `number_of_preemption_points_in_task_at_least_two_correspondence`

## Official Rocq

```coq
number_of_preemption_points_in_task_at_least_two :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskPreemptionPoints Task} {Job : JobType}
  {H1 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job)
  (ts : seq (Equality.sort Task)),
@valid_fixed_preemption_points_model Task H H0 Job H1 H3 H4 arr_seq ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
is_true (0 < @task_cost Task H tsk) -> is_true (1 < @size work (@task_preemption_points Task H0 tsk))

number_of_preemption_points_in_task_at_least_two is not universe polymorphic
Arguments number_of_preemption_points_in_task_at_least_two {Task H H0 Job H1 H3 H4} 
  arr_seq ts%seq_scope H_valid_fixed_preemption_points_model tsk H_tsk_in_ts H_positive_cost
number_of_preemption_points_in_task_at_least_two is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.limited.number_of_preemption_points_in_task_at_least_two
Declared in library prosa.analysis.facts.preemption.rtc_threshold.limited, line 62, characters 9-57
@number_of_preemption_points_in_task_at_least_two
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskPreemptionPoints Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)),
       @valid_fixed_preemption_points_model Task H H0 Job H1 H3 H4 arr_seq ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       is_true (0 < @task_cost Task H tsk) -> is_true (1 < @size work (@task_preemption_points Task H0 tsk))
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.number_of_preemption_points_in_task_at_least_two : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  [inst_6 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model arr_seq ts →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        0 < Prosa.Model.Task.Concept.task_cost tsk →
          1 < (Prosa.Model.Task.Preemption.Parameters.task_preemption_points tsk).length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Limited_number_of_preemption_points_in_task_at_least_two
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
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_7
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
         (List_length_inst1 Prosa_Behavior_Job_work
            (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task
               inst_7
               inst_13 tsk))
```
