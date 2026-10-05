# `in_task_arrivals_between_implies_job_of_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.in_task_arrivals_between_implies_job_of_task`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.in_task_arrivals_between_implies_job_of_task`
- Certificate: `in_task_arrivals_between_implies_job_of_task_correspondence`

## Official Rocq

```coq
in_task_arrivals_between_implies_job_of_task :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) -> @job_task Job Task H j = tsk

in_task_arrivals_between_implies_job_of_task is not universe polymorphic
Arguments in_task_arrivals_between_implies_job_of_task {Job Task H} arr_seq tsk t1 t2 j _
in_task_arrivals_between_implies_job_of_task is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.in_task_arrivals_between_implies_job_of_task
Declared in library prosa.analysis.facts.model.task_arrivals, line 179, characters 8-52
@in_task_arrivals_between_implies_job_of_task
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
       is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) -> @job_task Job Task H j = tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.in_task_arrivals_between_implies_job_of_task : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant)
  (j : Job),
  decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2) = true →
    Prosa.Model.Task.Concept.job_task j = tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_in_task_arrivals_between_implies_job_of_task
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
         (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant) (j : Job),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Model_Task_Arrivals_task_arrivals_between Job
                  inst_3 Task
                  inst_7
                  inst_10 arr_seq tsk t1
                  t2)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Model_Task_Arrivals_task_arrivals_between Job
                  inst_3 Task
                  inst_7
                  inst_10 arr_seq tsk t1
                  t2)))
         Bool_true ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_3 Task
            inst_7
            inst_10 j)
         tsk
```
