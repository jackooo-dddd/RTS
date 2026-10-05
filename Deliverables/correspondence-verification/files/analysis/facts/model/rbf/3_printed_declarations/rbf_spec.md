# `rbf_spec`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.rbf_spec`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.rbf_spec`
- Certificate: `rbf_spec_correspondence`

## Official Rocq

```coq
rbf_spec :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H3 : JobCost Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall tsk : Equality.sort Task,
@respects_max_arrivals Task Job H1 arr_seq tsk (@max_arrivals Task H0 tsk) ->
forall (t : instant) (Δ : nat),
is_true
  (@task_workload_between Task Job H1 H3 arr_seq tsk t (t + Δ) <=
   @task_request_bound_function Task H H0 tsk Δ)

rbf_spec is not universe polymorphic
Arguments rbf_spec {Task H H0 Job H1 H3} arr_seq H_valid_job_cost tsk H_tsk_arrivals_bounded t Δ%nat_scope
rbf_spec is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.rbf_spec
Declared in library prosa.analysis.facts.model.rbf, line 67, characters 10-18
@rbf_spec
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H3 : JobCost Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_max_arrivals Task Job H1 arr_seq tsk (@max_arrivals Task H0 tsk) ->
       forall (t : instant) (Δ : nat),
       is_true
         (@task_workload_between Task Job H1 H3 arr_seq tsk t (t + Δ) <=
          @task_request_bound_function Task H H0 tsk Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.rbf_spec : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Curves.respects_max_arrivals arr_seq tsk
          (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
        ∀ (t : Prosa.Behavior.Time.instant) (Δ : ℕ),
          Prosa.Model.Aggregate.Workload.task_workload_between arr_seq tsk t (t + Δ) ≤
            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_rbf_spec
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
       forall tsk : Task,
       Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task
         inst_3 Job
         inst_13
         inst_16 arr_seq tsk
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9 tsk) ->
       forall (t : Prosa_Behavior_Time_instant) (_UU0394_ : Nat),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_task_workload_between Task
            inst_3 Job
            inst_13
            inst_16
            inst_20 arr_seq tsk t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
               (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU0394_))
         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
            inst_3
            inst_6
            inst_9 tsk _UU0394_)
```
