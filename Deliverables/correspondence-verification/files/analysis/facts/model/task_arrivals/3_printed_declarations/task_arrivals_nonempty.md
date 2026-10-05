# `task_arrivals_nonempty`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.task_arrivals_nonempty`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_nonempty`
- Certificate: `task_arrivals_nonempty_correspondence`

## Official Rocq

```coq
task_arrivals_nonempty :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) -> is_true (t1 < t2)

task_arrivals_nonempty is not universe polymorphic
Arguments task_arrivals_nonempty {Job Task H} arr_seq tsk t1 t2 j _
task_arrivals_nonempty is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.task_arrivals_nonempty
Declared in library prosa.analysis.facts.model.task_arrivals, line 190, characters 8-30
@task_arrivals_nonempty
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
       is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) -> is_true (t1 < t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_nonempty : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2) = true → t1 < t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_nonempty
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
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t2
```
