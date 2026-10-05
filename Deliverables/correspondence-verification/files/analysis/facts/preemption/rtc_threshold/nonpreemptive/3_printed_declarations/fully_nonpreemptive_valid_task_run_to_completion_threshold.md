# `fully_nonpreemptive_valid_task_run_to_completion_threshold`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold`
- Certificate: `fully_nonpreemptive_valid_task_run_to_completion_threshold_correspondence`

## Official Rocq

```coq
fully_nonpreemptive_valid_task_run_to_completion_threshold :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H2 : JobCost Job} (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task),
is_true (0 < @task_cost Task H tsk) ->
@valid_task_run_to_completion_threshold Task H Job H0 H2 (@fully_nonpreemptive_job_model Job H2)
  (@fully_nonpreemptive_rtc_threshold Task) arr_seq tsk

fully_nonpreemptive_valid_task_run_to_completion_threshold is not universe polymorphic
Arguments fully_nonpreemptive_valid_task_run_to_completion_threshold {Task H Job H0 H2} 
  arr_seq tsk H_positive_cost
fully_nonpreemptive_valid_task_run_to_completion_threshold is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold
Declared in library prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive, line 69, characters 8-66
@fully_nonpreemptive_valid_task_run_to_completion_threshold
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H2 : JobCost Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task),
       is_true (0 < @task_cost Task H tsk) ->
       @valid_task_run_to_completion_threshold Task H Job H0 H2 (@fully_nonpreemptive_job_model Job H2)
         (@fully_nonpreemptive_rtc_threshold Task) arr_seq tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task),
  0 < Prosa.Model.Task.Concept.task_cost tsk →
    Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Nonpreemptive_fully_nonpreemptive_valid_task_run_to_completion_threshold
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10
            Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10)
         (tsk : Task),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_6
            tsk) ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
            inst_10
            inst_17)
         (Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_rtc_threshold Task
            inst_3)
         arr_seq tsk
```
