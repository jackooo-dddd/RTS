# `prev_job_in_task_arrivals_up_to_j`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.prev_job_in_task_arrivals_up_to_j`
- Lean: `Prosa.Analysis.Facts.JobIndex.prev_job_in_task_arrivals_up_to_j`
- Certificate: `prev_job_in_task_arrivals_up_to_j_correspondence`

## Official Rocq

```coq
prev_job_in_task_arrivals_up_to_j :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@prev_job Job Task H H0 arr_seq j \in @task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j)

prev_job_in_task_arrivals_up_to_j is not universe polymorphic
Arguments prev_job_in_task_arrivals_up_to_j {Task Job H H0} arr_seq H_valid_arrival_sequence 
  j H_arrives_in_arr_seq
prev_job_in_task_arrivals_up_to_j is opaque
Expands to: Constant prosa.analysis.facts.job_index.prev_job_in_task_arrivals_up_to_j
Declared in library prosa.analysis.facts.job_index, line 285, characters 8-41
@prev_job_in_task_arrivals_up_to_j
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true
         (@prev_job Job Task H H0 arr_seq j \in @task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j)
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.prev_job_in_task_arrivals_up_to_j : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        decide
            (Prosa.Model.Task.Arrivals.prev_job arr_seq j ∈
              Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j) =
          true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_prev_job_in_task_arrivals_up_to_j
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (inst_14 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
                  inst_7 Task
                  inst_3
                  inst_10
                  inst_14 arr_seq j)
               (Prosa_Model_Task_Arrivals_prev_job Job
                  inst_7 Task
                  inst_3
                  inst_10
                  inst_14 arr_seq j))
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job inst_7)
               (instLawfulBEq Job inst_7)
               (Prosa_Model_Task_Arrivals_prev_job Job
                  inst_7 Task
                  inst_3
                  inst_10
                  inst_14 arr_seq j)
               (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
                  inst_7 Task
                  inst_3
                  inst_10
                  inst_14 arr_seq j)))
         Bool_true
```
