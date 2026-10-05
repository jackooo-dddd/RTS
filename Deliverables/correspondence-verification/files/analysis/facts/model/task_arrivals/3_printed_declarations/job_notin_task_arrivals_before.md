# `job_notin_task_arrivals_before`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.job_notin_task_arrivals_before`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.job_notin_task_arrivals_before`
- Certificate: `job_notin_task_arrivals_before_correspondence`

## Official Rocq

```coq
job_notin_task_arrivals_before :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (j : Equality.sort Job) (t : nat),
@arrives_in Job arr_seq j ->
is_true (t < @job_arrival Job H0 j) ->
is_true (j \notin @task_arrivals_up_to Job Task H arr_seq (@job_task Job Task H j) t)

job_notin_task_arrivals_before is not universe polymorphic
Arguments job_notin_task_arrivals_before {Job Task H H0} arr_seq H_consistent_arrivals j t%nat_scope _ _
job_notin_task_arrivals_before is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.job_notin_task_arrivals_before
Declared in library prosa.analysis.facts.model.task_arrivals, line 223, characters 8-38
@job_notin_task_arrivals_before
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (j : Equality.sort Job) (t : nat),
       @arrives_in Job arr_seq j ->
       is_true (t < @job_arrival Job H0 j) ->
       is_true (j \notin @task_arrivals_up_to Job Task H arr_seq (@job_task Job Task H j) t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.job_notin_task_arrivals_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t : ℕ),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        t < Prosa.Behavior.Job.job_arrival j →
          (!decide
                (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_up_to arr_seq (Prosa.Model.Task.Concept.job_task j) t)) =
            true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_job_notin_task_arrivals_before
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
       forall (j : Job) (t : Nat),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       LT_lt_inst1 Nat instLTNat t
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_14 j) ->
       @eq Bool
         (Bool_not
            (Decidable_decide
               (Membership_mem Job (List Job) (List_instMembership Job)
                  (Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
                     inst_3 Task
                     inst_7
                     inst_10 arr_seq
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_3 Task
                        inst_7
                        inst_10 j)
                     t)
                  j)
               (List_instDecidableMemOfLawfulBEq Job
                  (instBEqOfDecidableEq Job
                     inst_3)
                  (instLawfulBEq Job
                     inst_3)
                  j
                  (Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
                     inst_3 Task
                     inst_7
                     inst_10 arr_seq
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_3 Task
                        inst_7
                        inst_10 j)
                     t))))
         Bool_true
```
