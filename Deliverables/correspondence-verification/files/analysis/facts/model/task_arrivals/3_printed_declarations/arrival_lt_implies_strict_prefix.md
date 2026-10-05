# `arrival_lt_implies_strict_prefix`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.arrival_lt_implies_strict_prefix`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.arrival_lt_implies_strict_prefix`
- Certificate: `arrival_lt_implies_strict_prefix_correspondence`

## Official Rocq

```coq
arrival_lt_implies_strict_prefix :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (tsk : Equality.sort Task) (j1 j2 : Equality.sort Job),
@job_task Job Task H j1 = tsk ->
@job_task Job Task H j2 = tsk ->
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
is_true (@job_arrival Job H0 j1 < @job_arrival Job H0 j2) ->
@strict_prefix_of Job (@task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j1)
  (@task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j2)

arrival_lt_implies_strict_prefix is not universe polymorphic
Arguments arrival_lt_implies_strict_prefix {Job Task H H0} arr_seq H_consistent_arrivals tsk j1 j2 _ _ _ _ _
arrival_lt_implies_strict_prefix is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.arrival_lt_implies_strict_prefix
Declared in library prosa.analysis.facts.model.task_arrivals, line 238, characters 8-40
@arrival_lt_implies_strict_prefix
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (tsk : Equality.sort Task) (j1 j2 : Equality.sort Job),
       @job_task Job Task H j1 = tsk ->
       @job_task Job Task H j2 = tsk ->
       @arrives_in Job arr_seq j1 ->
       @arrives_in Job arr_seq j2 ->
       is_true (@job_arrival Job H0 j1 < @job_arrival Job H0 j2) ->
       @strict_prefix_of Job (@task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j1)
         (@task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.arrival_lt_implies_strict_prefix : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (tsk : Task) (j1 j2 : Job),
      Prosa.Model.Task.Concept.job_task j1 = tsk →
        Prosa.Model.Task.Concept.job_task j2 = tsk →
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
              Prosa.Behavior.Job.job_arrival j1 < Prosa.Behavior.Job.job_arrival j2 →
                Prosa.Util.List.strict_prefix_of (Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j1)
                  (Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_arrival_lt_implies_strict_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_14 arr_seq ->
       forall (tsk : Task) (j1 j2 : Job),
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_3 Task
            inst_7
            inst_10 j1)
         tsk ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_3 Task
            inst_7
            inst_10 j2)
         tsk ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j1 ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j2 ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_14 j1)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_14 j2) ->
       Prosa_Util_List_strict_prefix_of Job
         inst_3
         (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
            inst_3 Task
            inst_7
            inst_10
            inst_14 arr_seq j1)
         (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
            inst_3 Task
            inst_7
            inst_10
            inst_14 arr_seq j2)
```
