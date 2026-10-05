# `nth_job_of_task_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.nth_job_of_task_arrivals`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.nth_job_of_task_arrivals`
- Certificate: `nth_job_of_task_arrivals_correspondence`

## Official Rocq

```coq
nth_job_of_task_arrivals :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (tsk : Equality.sort Task) (n : nat) (j_def j : Equality.sort Job) (t : nat),
@arrives_in Job arr_seq j ->
@job_task Job Task H j = tsk ->
@job_index Task Job H0 H arr_seq j = n ->
is_true (@job_arrival Job H0 j <= t) ->
@nth (Equality.sort Job) j_def (@task_arrivals_up_to Job Task H arr_seq tsk t) n = j

nth_job_of_task_arrivals is not universe polymorphic
Arguments nth_job_of_task_arrivals {Job Task H H0} arr_seq H_consistent_arrivals 
  tsk n%nat_scope j_def j t%nat_scope _ _ _ _
nth_job_of_task_arrivals is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.nth_job_of_task_arrivals
Declared in library prosa.analysis.facts.model.task_arrivals, line 262, characters 8-32
@nth_job_of_task_arrivals
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (tsk : Equality.sort Task) (n : nat) (j_def j : Equality.sort Job) (t : nat),
       @arrives_in Job arr_seq j ->
       @job_task Job Task H j = tsk ->
       @job_index Task Job H0 H arr_seq j = n ->
       is_true (@job_arrival Job H0 j <= t) ->
       @nth (Equality.sort Job) j_def (@task_arrivals_up_to Job Task H arr_seq tsk t) n = j
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.nth_job_of_task_arrivals : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (tsk : Task) (n : ℕ) (j_def j : Job) (t : ℕ),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Task.Concept.job_task j = tsk →
          Prosa.Model.Task.Arrivals.job_index arr_seq j = n →
            Prosa.Behavior.Job.job_arrival j ≤ t →
              (Prosa.Model.Task.Arrivals.task_arrivals_up_to arr_seq tsk t).getD n j_def = j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_nth_job_of_task_arrivals
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
       forall (tsk : Task) (n : Nat) (j_def j : Job) (t : Nat),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_3 Task
            inst_7
            inst_10 j)
         tsk ->
       @eq Nat
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_7 Job
            inst_3
            inst_14
            inst_10 arr_seq j)
         n ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_14 j)
         t ->
       @eq Job
         (List_getD Job
            (Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t)
            n j_def)
         j
```
