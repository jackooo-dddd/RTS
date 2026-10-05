# `arrives_in_task_arrivals_before_implies_arrives_before`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_before_implies_arrives_before`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_before_implies_arrives_before`
- Certificate: `arrives_in_task_arrivals_before_implies_arrives_before_correspondence`

## Official Rocq

```coq
arrives_in_task_arrivals_before_implies_arrives_before :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t : instant),
is_true (j \in @task_arrivals_before Job Task H arr_seq tsk t) -> is_true (@job_arrival Job H0 j < t)

arrives_in_task_arrivals_before_implies_arrives_before is not universe polymorphic
Arguments arrives_in_task_arrivals_before_implies_arrives_before {Job Task H H0} 
  arr_seq H_consistent_arrivals tsk j t _
arrives_in_task_arrivals_before_implies_arrives_before is opaque
Expands to: Constant
            prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_before_implies_arrives_before
Declared in library prosa.analysis.facts.model.task_arrivals, line 156, characters 8-62
@arrives_in_task_arrivals_before_implies_arrives_before
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t : instant),
       is_true (j \in @task_arrivals_before Job Task H arr_seq tsk t) -> is_true (@job_arrival Job H0 j < t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_before_implies_arrives_before : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (tsk : Task) (j : Job) (t : Prosa.Behavior.Time.instant),
      decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_before arr_seq tsk t) = true →
        Prosa.Behavior.Job.job_arrival j < t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_before_implies_arrives_before
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
       forall (tsk : Task) (j : Job) (t : Prosa_Behavior_Time_instant),
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
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_14 j)
         t
```
