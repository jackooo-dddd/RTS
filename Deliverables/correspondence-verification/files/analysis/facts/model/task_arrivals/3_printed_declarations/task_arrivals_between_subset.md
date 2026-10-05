# `task_arrivals_between_subset`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.task_arrivals_between_subset`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_subset`
- Certificate: `task_arrivals_between_subset_correspondence`

## Official Rocq

```coq
task_arrivals_between_subset :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) ->
is_true (j \in @arrivals_between Job arr_seq t1 t2)

task_arrivals_between_subset is not universe polymorphic
Arguments task_arrivals_between_subset {Job Task H} arr_seq tsk t1 t2 j _
task_arrivals_between_subset is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.task_arrivals_between_subset
Declared in library prosa.analysis.facts.model.task_arrivals, line 140, characters 8-36
@task_arrivals_between_subset
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
       is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) ->
       is_true (j \in @arrivals_between Job arr_seq t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_subset : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2) = true →
    decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_subset
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
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t2)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t2)))
         Bool_true
```
