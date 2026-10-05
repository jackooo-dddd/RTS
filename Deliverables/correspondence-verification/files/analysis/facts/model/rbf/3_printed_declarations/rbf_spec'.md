# `rbf_spec'`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.rbf.rbf_spec'`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.rbf_spec'`
- Certificate: `rbf_spec'_correspondence`

## Official Rocq

```coq
rbf_spec' :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H3 : JobCost Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall (P : pred (Equality.sort Job)) (tsk : Equality.sort Task),
@respects_max_arrivals Task Job H1 arr_seq tsk (@max_arrivals Task H0 tsk) ->
(forall j : Equality.sort Job, is_true (P j) -> is_true (@job_of_task Job Task H1 tsk j)) ->
forall (t : instant) (Δ : nat),
is_true
  (@workload_of_jobs Job H3 P (@arrivals_between Job arr_seq t (t + Δ)) <=
   @task_request_bound_function Task H H0 tsk Δ)

rbf_spec' is not universe polymorphic
Arguments rbf_spec' {Task H H0 Job H1 H3} arr_seq H_valid_job_cost P tsk H_tsk_arrivals_bounded
  H_jobs_of_tsk%function_scope t Δ%nat_scope
rbf_spec' is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.rbf_spec'
Declared in library prosa.analysis.facts.model.rbf, line 99, characters 14-23
@rbf_spec'
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H3 : JobCost Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall (P : pred (Equality.sort Job)) (tsk : Equality.sort Task),
       @respects_max_arrivals Task Job H1 arr_seq tsk (@max_arrivals Task H0 tsk) ->
       (forall j : Equality.sort Job, is_true (P j) -> is_true (@job_of_task Job Task H1 tsk j)) ->
       forall (t : instant) (Δ : nat),
       is_true
         (@workload_of_jobs Job H3 P (@arrivals_between Job arr_seq t (t + Δ)) <=
          @task_request_bound_function Task H H0 tsk Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.rbf_spec' : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (P : Job → Bool) (tsk : Task),
      Prosa.Model.Task.Arrival.Curves.respects_max_arrivals arr_seq tsk
          (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
        (∀ (j : Job), P j = true → Prosa.Model.Task.Concept.job_of_task tsk j = true) →
          ∀ (t : Prosa.Behavior.Time.instant) (Δ : ℕ),
            Prosa.Model.Aggregate.Workload.workload_of_jobs P
                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t (t + Δ)) ≤
              Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_rbf_spec'
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
       forall (P : Job -> Bool) (tsk : Task),
       Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task
         inst_3 Job
         inst_13
         inst_16 arr_seq tsk
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9 tsk) ->
       (forall j : Job,
        @eq Bool (P j) Bool_true ->
        @eq Bool
          (Prosa_Model_Task_Concept_job_of_task Job
             inst_13 Task
             inst_3
             inst_16 tsk j)
          Bool_true) ->
       forall (t : Prosa_Behavior_Time_instant) (_UU0394_ : Nat),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_13
            inst_20 P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_13 arr_seq t
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU0394_)))
         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
            inst_3
            inst_6
            inst_9 tsk _UU0394_)
```
