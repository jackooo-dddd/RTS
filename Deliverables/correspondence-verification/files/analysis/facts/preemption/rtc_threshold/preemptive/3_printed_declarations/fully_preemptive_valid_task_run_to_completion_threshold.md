# `fully_preemptive_valid_task_run_to_completion_threshold`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.preemptive.fully_preemptive_valid_task_run_to_completion_threshold`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive.fully_preemptive_valid_task_run_to_completion_threshold`
- Certificate: `fully_preemptive_valid_task_run_to_completion_threshold_correspondence`

## Official Rocq

```coq
fully_preemptive_valid_task_run_to_completion_threshold :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobCost Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H0 H1 arr_seq ->
forall tsk : Equality.sort Task,
@valid_task_run_to_completion_threshold Task H Job H0 H1 (@fully_preemptive_job_model Job)
  (@fully_preemptive_rtc_threshold Task H) arr_seq tsk

fully_preemptive_valid_task_run_to_completion_threshold is not universe polymorphic
Arguments fully_preemptive_valid_task_run_to_completion_threshold {Task H Job H0 H1} 
  arr_seq H_valid_job_cost tsk
fully_preemptive_valid_task_run_to_completion_threshold is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.preemptive.fully_preemptive_valid_task_run_to_completion_threshold
Declared in library prosa.analysis.facts.preemption.rtc_threshold.preemptive, line 34, characters 8-63
@fully_preemptive_valid_task_run_to_completion_threshold
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobCost Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H0 H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @valid_task_run_to_completion_threshold Task H Job H0 H1 (@fully_preemptive_job_model Job)
         (@fully_preemptive_rtc_threshold Task H) arr_seq tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive.fully_preemptive_valid_task_run_to_completion_threshold : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (tsk : Task), Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Preemptive_fully_preemptive_valid_task_run_to_completion_threshold
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
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq ->
       forall tsk : Task,
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
            inst_10)
         (Prosa_Model_Task_Preemption_FullyPreemptive_fully_preemptive_rtc_threshold Task
            inst_3
            inst_6)
         arr_seq tsk
```
