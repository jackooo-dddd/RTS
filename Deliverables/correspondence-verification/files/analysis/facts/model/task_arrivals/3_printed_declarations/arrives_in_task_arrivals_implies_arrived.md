# `arrives_in_task_arrivals_implies_arrived`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_arrived`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_implies_arrived`
- Certificate: `arrives_in_task_arrivals_implies_arrived_correspondence`

## Official Rocq

```coq
arrives_in_task_arrivals_implies_arrived :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) -> @arrives_in Job arr_seq j

arrives_in_task_arrivals_implies_arrived is not universe polymorphic
Arguments arrives_in_task_arrivals_implies_arrived {Job Task H} arr_seq tsk t1 t2 j _
arrives_in_task_arrivals_implies_arrived is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_arrived
Declared in library prosa.analysis.facts.model.task_arrivals, line 148, characters 12-52
@arrives_in_task_arrivals_implies_arrived
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t2 : instant) (j : Equality.sort Job),
       is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2) -> @arrives_in Job arr_seq j
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_implies_arrived : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2) = true →
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_implies_arrived
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
                  inst_10 arr_seq tsk
                  t1 t2)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job
                  inst_3)
               j
               (Prosa_Model_Task_Arrivals_task_arrivals_between Job
                  inst_3 Task
                  inst_7
                  inst_10 arr_seq tsk
                  t1 t2)))
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j
```
