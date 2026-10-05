# `arrives_in_task_arrivals_implies_job_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_job_task`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_implies_job_task`
- Certificate: `arrives_in_task_arrivals_implies_job_task_correspondence`

## Official Rocq

```coq
arrives_in_task_arrivals_implies_job_task :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (j : Equality.sort Job) (t : instant),
is_true (j \in @task_arrivals_before Job Task H arr_seq tsk t) -> is_true (@job_task Job Task H j == tsk)

arrives_in_task_arrivals_implies_job_task is not universe polymorphic
Arguments arrives_in_task_arrivals_implies_job_task {Job Task H} arr_seq tsk j t _
arrives_in_task_arrivals_implies_job_task is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_job_task
Declared in library prosa.analysis.facts.model.task_arrivals, line 168, characters 8-49
@arrives_in_task_arrivals_implies_job_task
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (j : Equality.sort Job) (t : instant),
       is_true (j \in @task_arrivals_before Job Task H arr_seq tsk t) ->
       is_true (@job_task Job Task H j == tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_implies_job_task : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (tsk : Task) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_before arr_seq tsk t) = true →
    decide (Prosa.Model.Task.Concept.job_task j = tsk) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_implies_job_task
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (tsk : Task) (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Model_Task_Arrivals_task_arrivals_before Job
                  inst_3 Task
                  inst_7
                  inst_10 arr_seq tsk t)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job
                  inst_3)
               j
               (Prosa_Model_Task_Arrivals_task_arrivals_before Job
                  inst_3 Task
                  inst_7
                  inst_10 arr_seq tsk t)))
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (@eq Task
               (Prosa_Model_Task_Concept_JobTask_job_task Job
                  inst_3 Task
                  inst_7
                  inst_10 j)
               tsk)
            (inst_7
               (Prosa_Model_Task_Concept_JobTask_job_task Job
                  inst_3 Task
                  inst_7
                  inst_10 j)
               tsk))
         Bool_true
```
