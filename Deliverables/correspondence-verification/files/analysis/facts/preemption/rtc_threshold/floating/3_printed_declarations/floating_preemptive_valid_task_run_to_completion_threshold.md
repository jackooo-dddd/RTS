# `floating_preemptive_valid_task_run_to_completion_threshold`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.floating.floating_preemptive_valid_task_run_to_completion_threshold`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating.floating_preemptive_valid_task_run_to_completion_threshold`
- Certificate: `floating_preemptive_valid_task_run_to_completion_threshold_correspondence`

## Official Rocq

```coq
floating_preemptive_valid_task_run_to_completion_threshold :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobCost Job} {H2 : JobPreemptable Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H0 H1 arr_seq ->
forall tsk : Equality.sort Task,
@valid_task_run_to_completion_threshold Task H Job H0 H1 H2 (@floating_preemptive_rtc_threshold Task H)
  arr_seq tsk

floating_preemptive_valid_task_run_to_completion_threshold is not universe polymorphic
Arguments floating_preemptive_valid_task_run_to_completion_threshold {Task H Job H0 H1 H2} 
  arr_seq H_valid_job_cost tsk
floating_preemptive_valid_task_run_to_completion_threshold is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.floating.floating_preemptive_valid_task_run_to_completion_threshold
Declared in library prosa.analysis.facts.preemption.rtc_threshold.floating, line 32, characters 8-66
@floating_preemptive_valid_task_run_to_completion_threshold
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobCost Job) (H2 : JobPreemptable Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H0 H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @valid_task_run_to_completion_threshold Task H Job H0 H1 H2
         (@floating_preemptive_rtc_threshold Task H) arr_seq tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating.floating_preemptive_valid_task_run_to_completion_threshold : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  [inst_5 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (tsk : Task), Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Floating_floating_preemptive_valid_task_run_to_completion_threshold
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
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_20 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_7
         inst_10 Job
         inst_3
         inst_13
         inst_17 arr_seq ->
       forall tsk : Task,
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_7
         inst_10 Job
         inst_3
         inst_13
         inst_17
         inst_20
         (Prosa_Model_Task_Preemption_FloatingNonpreemptive_floating_preemptive_rtc_threshold Task
            inst_7
            inst_10)
         arr_seq tsk
```
