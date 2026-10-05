# `job_in_task_arrivals_between`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.job_in_task_arrivals_between`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.job_in_task_arrivals_between`
- Certificate: `job_in_task_arrivals_between_correspondence`

## Official Rocq

```coq
job_in_task_arrivals_between :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t1 t2 : nat),
@arrives_in Job arr_seq j ->
@job_task Job Task H j = tsk ->
is_true (t1 <= @job_arrival Job H0 j < t2) ->
is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2)

job_in_task_arrivals_between is not universe polymorphic
Arguments job_in_task_arrivals_between {Job Task H H0} arr_seq H_consistent_arrivals 
  tsk j (t1 t2)%nat_scope _ _ _
job_in_task_arrivals_between is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.job_in_task_arrivals_between
Declared in library prosa.analysis.facts.model.task_arrivals, line 125, characters 8-36
@job_in_task_arrivals_between
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t1 t2 : nat),
       @arrives_in Job arr_seq j ->
       @job_task Job Task H j = tsk ->
       is_true (t1 <= @job_arrival Job H0 j < t2) ->
       is_true (j \in @task_arrivals_between Job Task H arr_seq tsk t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.job_in_task_arrivals_between : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (tsk : Task) (j : Job) (t1 t2 : ℕ),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Task.Concept.job_task j = tsk →
          (decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) && decide (Prosa.Behavior.Job.job_arrival j < t2)) = true →
            decide (j ∈ Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_job_in_task_arrivals_between
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
       forall (tsk : Task) (j : Job) (t1 t2 : Nat),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_3 Task
            inst_7
            inst_10 j)
         tsk ->
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Nat instLENat t1
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_14 j))
               (Nat_decLe t1
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_14 j)))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_14 j)
                  t2)
               (Nat_decLt
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_14 j)
                  t2)))
         Bool_true ->
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
         Bool_true
```
