# `ohep_workload_le_rbf`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.ohep_workload_le_rbf`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.ohep_workload_le_rbf`
- Certificate: `ohep_workload_le_rbf_correspondence`

## Official Rocq

```coq
ohep_workload_le_rbf :
forall {Task : TaskType} {H : TaskCost Task} (ts : seq (Equality.sort Task)) {H1 : FP_policy Task}
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobCost Job} (arr_seq : arrival_sequence Job),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@arrivals_have_valid_job_costs Task H Job H2 H3 arr_seq ->
forall {H4 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H2 arr_seq H4 ts ->
forall (j : Equality.sort Job) (tsk : Equality.sort Task),
is_true (@job_of_task Job Task H2 tsk j) ->
forall (Δ : nat) (t1 : instant),
is_true
  (@workload_of_jobs Job H3 ((@another_task_hep_job Task Job H2 (@FP_to_JLFP Job Task H2 H1))^~ j)
     (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
   @total_ohep_request_bound_function_FP Task H H4 ts H1 tsk Δ)

ohep_workload_le_rbf is not universe polymorphic
Arguments ohep_workload_le_rbf {Task H} ts%seq_scope {H1 Job H2 H3} arr_seq H_all_jobs_from_taskset
  H_valid_job_cost {H4} H_respects_max_arrivals j tsk H_job_of_task Δ%nat_scope t1
ohep_workload_le_rbf is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.ohep_workload_le_rbf
Declared in library prosa.analysis.facts.model.rbf, line 644, characters 8-28
@ohep_workload_le_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (ts : seq (Equality.sort Task)) 
         (H1 : FP_policy Task) (Job : JobType) (H2 : JobTask Job Task) (H3 : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H Job H2 H3 arr_seq ->
       forall H4 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H2 arr_seq H4 ts ->
       forall (j : Equality.sort Job) (tsk : Equality.sort Task),
       is_true (@job_of_task Job Task H2 tsk j) ->
       forall (Δ : nat) (t1 : instant),
       is_true
         (@workload_of_jobs Job H3 ((@another_task_hep_job Task Job H2 (@FP_to_JLFP Job Task H2 H1))^~ j)
            (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
          @total_ohep_request_bound_function_FP Task H H4 ts H1 tsk Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.ohep_workload_le_rbf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] (ts : List Task)
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task) {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ [inst_5 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
        Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
          ∀ (j : Job) (tsk : Task),
            Prosa.Model.Task.Concept.job_of_task tsk j = true →
              ∀ (Δ : ℕ) (t1 : Prosa.Behavior.Time.instant),
                Prosa.Model.Aggregate.Workload.workload_of_jobs
                    (fun j' => Prosa.Model.Priority.Definitions.another_task_hep_job j' j)
                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) ≤
                  Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP ts tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_ohep_workload_le_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (ts : List Task)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_14 : DecidableEq Job)
         (inst_17 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_14 Task
            inst_3)
         (inst_21 : 
          Prosa_Behavior_Job_JobCost Job inst_14)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_14),
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_14
         inst_17 arr_seq ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_14
         inst_17
         inst_21 arr_seq ->
       forall
         inst_36 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_14
         inst_17 arr_seq
         inst_36 ts ->
       forall (j : Job) (tsk : Task),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_14 Task
            inst_3
            inst_17 tsk j)
         Bool_true ->
       forall (_UU0394_ : Nat) (t1 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_14
            inst_21
            (fun j' : Job =>
             Prosa_Model_Priority_Definitions_another_task_hep_job Task
               inst_3 Job
               inst_14
               inst_17
               (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
                  inst_14 Task
                  inst_3
                  inst_17 FP)
               j' j)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_14 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)))
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP Task
            inst_3
            inst_6
            inst_36 ts FP tsk _UU0394_)
```
