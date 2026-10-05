# `task_arrivals_up_to_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_cat`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_up_to_cat`
- Certificate: `task_arrivals_up_to_cat_correspondence`

## Official Rocq

```coq
task_arrivals_up_to_cat :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
@task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j =
@task_arrivals_before_job_arrival Job Task H H0 arr_seq j ++
@task_arrivals_at_job_arrival Job Task H H0 arr_seq j

task_arrivals_up_to_cat is not universe polymorphic
Arguments task_arrivals_up_to_cat {Job Task H H0} arr_seq j _
task_arrivals_up_to_cat is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_cat
Declared in library prosa.analysis.facts.model.task_arrivals, line 109, characters 8-31
@task_arrivals_up_to_cat
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       @task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j =
       @task_arrivals_before_job_arrival Job Task H H0 arr_seq j ++
       @task_arrivals_at_job_arrival Job Task H H0 arr_seq j
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_up_to_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (j : Job),
  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
    Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j =
      Prosa.Model.Task.Arrivals.task_arrivals_before_job_arrival arr_seq j ++
        Prosa.Model.Task.Arrivals.task_arrivals_at_job_arrival arr_seq j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_up_to_cat
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
                      inst_3)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq (List Job)
         (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
            inst_3 Task
            inst_7
            inst_10
            inst_14 arr_seq j)
         (HAppend_hAppend (List Job) (List Job) (List Job)
            (instHAppendOfAppend (List Job) (List_instAppend Job))
            (Prosa_Model_Task_Arrivals_task_arrivals_before_job_arrival Job
               inst_3 Task
               inst_7
               inst_10
               inst_14 arr_seq j)
            (Prosa_Model_Task_Arrivals_task_arrivals_at_job_arrival Job
               inst_3 Task
               inst_7
               inst_10
               inst_14 arr_seq j))
```
