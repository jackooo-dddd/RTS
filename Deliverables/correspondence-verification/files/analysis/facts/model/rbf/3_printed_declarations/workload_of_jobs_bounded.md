# `workload_of_jobs_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.workload_of_jobs_bounded`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.workload_of_jobs_bounded`
- Certificate: `workload_of_jobs_bounded_correspondence`

## Official Rocq

```coq
workload_of_jobs_bounded :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H3 : JobCost Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
forall (pred1 : pred (Equality.sort Job)) (pred2 : pred (Equality.sort Task)),
(forall j : Equality.sort Job, is_true (pred1 j) -> is_true (pred2 (@job_task Job Task H1 j))) ->
forall (t : instant) (Δ : nat),
is_true
  (@workload_of_jobs Job H3 pred1 (@arrivals_between Job arr_seq t (t + Δ)) <=
   \sum_(tsk' <- ts | pred2 tsk') @task_request_bound_function Task H H0 tsk' Δ)

workload_of_jobs_bounded is not universe polymorphic
Arguments workload_of_jobs_bounded {Task H H0 Job H1 H3} arr_seq H_valid_job_cost 
  ts%seq_scope H_all_jobs_from_taskset H_is_arrival_bound pred1 pred2 H_also_satisfied%function_scope 
  t Δ%nat_scope
workload_of_jobs_bounded is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.workload_of_jobs_bounded
Declared in library prosa.analysis.facts.model.rbf, line 151, characters 10-34
@workload_of_jobs_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H3 : JobCost Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
       forall (pred1 : pred (Equality.sort Job)) (pred2 : pred (Equality.sort Task)),
       (forall j : Equality.sort Job, is_true (pred1 j) -> is_true (pred2 (@job_task Job Task H1 j))) ->
       forall (t : instant) (Δ : nat),
       is_true
         (@workload_of_jobs Job H3 pred1 (@arrivals_between Job arr_seq t (t + Δ)) <=
          \sum_(tsk' <- ts | pred2 tsk') @task_request_bound_function Task H H0 tsk' Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.workload_of_jobs_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (ts : List Task),
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
        Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
          ∀ (pred1 : Job → Bool) (pred2 : Task → Bool),
            (∀ (j : Job), pred1 j = true → pred2 (Prosa.Model.Task.Concept.job_task j) = true) →
              ∀ (t : Prosa.Behavior.Time.instant) (Δ : ℕ),
                Prosa.Model.Aggregate.Workload.workload_of_jobs pred1
                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t (t + Δ)) ≤
                  Prosa.Util.Sum.sumFiltered ts pred2 fun tsk' =>
                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk' Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_workload_of_jobs_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_13
                                                                                Task
                                                                                inst_3)
         (inst_20 : Prosa_Behavior_Job_JobCost
                                                                                Job
                                                                                inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_20 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_13
         inst_16 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_13
         inst_16 arr_seq
         inst_9 ts ->
       forall (pred1 : Job -> Bool) (pred2 : Task -> Bool),
       (forall j : Job,
        @eq Bool (pred1 j) Bool_true ->
        @eq Bool
          (pred2
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_13 Task
                inst_3
                inst_16 j))
          Bool_true) ->
       forall (t : Prosa_Behavior_Time_instant) (_UU0394_ : Nat),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_13
            inst_20 pred1
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_13 arr_seq t
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU0394_)))
         (Prosa_Util_Sum_sumFiltered Task ts pred2
            (fun tsk' : Task =>
             Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
               inst_3
               inst_6
               inst_9 tsk' _UU0394_))
```
