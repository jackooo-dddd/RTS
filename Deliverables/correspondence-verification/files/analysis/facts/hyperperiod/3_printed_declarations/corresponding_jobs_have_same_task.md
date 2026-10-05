# `corresponding_jobs_have_same_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.hyperperiod.corresponding_jobs_have_same_task`
- Lean: `Prosa.Analysis.Facts.Hyperperiod.corresponding_jobs_have_same_task`
- Certificate: `corresponding_jobs_have_same_task_correspondence`

## Official Rocq

```coq
corresponding_jobs_have_same_task :
forall {Task : TaskType} {H : TaskOffset Task} {H0 : PeriodicModel Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobArrival Job} (arr_seq : arrival_sequence Job)
  (ts : TaskSet (Equality.sort Task)) (j1 j2 : Equality.sort Job),
@job_task Job Task H1
  (@corresponding_job_in_hyperperiod Task H H0 Job H1 H2 ts arr_seq j1
     (@starting_instant_of_corresponding_hyperperiod Task H H0 Job H2 ts j2) (@job_task Job Task H1 j1)) =
@job_task Job Task H1 j1

corresponding_jobs_have_same_task is not universe polymorphic
Arguments corresponding_jobs_have_same_task {Task H H0 Job H1 H2} arr_seq ts j1 j2
corresponding_jobs_have_same_task is opaque
Expands to: Constant prosa.analysis.facts.hyperperiod.corresponding_jobs_have_same_task
Declared in library prosa.analysis.facts.hyperperiod, line 93, characters 8-41
@corresponding_jobs_have_same_task
     : forall (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (ts : TaskSet (Equality.sort Task)) (j1 j2 : Equality.sort Job),
       @job_task Job Task H1
         (@corresponding_job_in_hyperperiod Task H H0 Job H1 H2 ts arr_seq j1
            (@starting_instant_of_corresponding_hyperperiod Task H H0 Job H2 ts j2)
            (@job_task Job Task H1 j1)) =
       @job_task Job Task H1 j1
```

## Lean

```lean
@Prosa.Analysis.Facts.Hyperperiod.corresponding_jobs_have_same_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task]
  [inst_2 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (ts : Prosa.Model.Task.Concept.TaskSet Task) (j1 j2 : Job),
  Prosa.Model.Task.Concept.job_task
      (Prosa.Analysis.Definitions.Hyperperiod.corresponding_job_in_hyperperiod ts arr_seq j1
        (Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_corresponding_hyperperiod ts j2)
        (Prosa.Model.Task.Concept.job_task j1)) =
    Prosa.Model.Task.Concept.job_task j1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Hyperperiod_corresponding_jobs_have_same_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Offset_TaskOffset Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13)
         (ts : Prosa_Model_Task_Concept_TaskSet Task) (j1 j2 : Job),
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_13 Task
            inst_3
            inst_16
            (Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod Task
               inst_3
               inst_6
               inst_9 Job
               inst_13
               inst_16
               inst_20 ts arr_seq j1
               (Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod Task
                  inst_3
                  inst_6
                  inst_9 Job
                  inst_13
                  inst_20 ts j2)
               (Prosa_Model_Task_Concept_JobTask_job_task Job
                  inst_13 Task
                  inst_3
                  inst_16 j1)))
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_13 Task
            inst_3
            inst_16 j1)
```
