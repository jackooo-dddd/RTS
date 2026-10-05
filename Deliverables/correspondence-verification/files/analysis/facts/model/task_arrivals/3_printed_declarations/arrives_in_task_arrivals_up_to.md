# `arrives_in_task_arrivals_up_to`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_up_to`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_up_to`
- Certificate: `arrives_in_task_arrivals_up_to_correspondence`

## Official Rocq

```coq
arrives_in_task_arrivals_up_to :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j -> is_true (j \in @task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j)

arrives_in_task_arrivals_up_to is not universe polymorphic
Arguments arrives_in_task_arrivals_up_to {Job Task H H0} arr_seq H_consistent_arrivals j _
arrives_in_task_arrivals_up_to is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_up_to
Declared in library prosa.analysis.facts.model.task_arrivals, line 64, characters 8-38
@arrives_in_task_arrivals_up_to
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j -> is_true (j \in @task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.arrives_in_task_arrivals_up_to : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_up_to
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
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
                  inst_3 Task
                  inst_7
                  inst_10
                  inst_14 arr_seq j)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job
                  inst_3)
               j
               (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
                  inst_3 Task
                  inst_7
                  inst_10
                  inst_14 arr_seq j)))
         Bool_true
```
