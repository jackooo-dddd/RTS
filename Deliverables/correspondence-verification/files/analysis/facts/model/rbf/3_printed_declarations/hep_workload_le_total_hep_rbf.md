# `hep_workload_le_total_hep_rbf`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.hep_workload_le_total_hep_rbf`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.hep_workload_le_total_hep_rbf`
- Certificate: `hep_workload_le_total_hep_rbf_correspondence`

## Official Rocq

```coq
hep_workload_le_total_hep_rbf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H3 : JobCost Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
forall {FP : FP_policy Task} (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H1 tsk j) ->
forall (t : instant) (Δ : nat),
is_true
  (@workload_of_hep_jobs Job H3 arr_seq (@FP_to_JLFP Job Task H1 FP) j t (t + Δ) <=
   @total_hep_request_bound_function_FP Task H H0 ts FP tsk Δ)

hep_workload_le_total_hep_rbf is not universe polymorphic
Arguments hep_workload_le_total_hep_rbf {Task H H0 Job H1 H3} arr_seq H_valid_job_cost 
  ts%seq_scope H_all_jobs_from_taskset H_is_arrival_bound {FP} tsk j H_job_of_tsk 
  t Δ%nat_scope
hep_workload_le_total_hep_rbf is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.hep_workload_le_total_hep_rbf
Declared in library prosa.analysis.facts.model.rbf, line 223, characters 10-39
@hep_workload_le_total_hep_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H3 : JobCost Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
       forall (FP : FP_policy Task) (tsk : Equality.sort Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H1 tsk j) ->
       forall (t : instant) (Δ : nat),
       is_true
         (@workload_of_hep_jobs Job H3 arr_seq (@FP_to_JLFP Job Task H1 FP) j t (t + Δ) <=
          @total_hep_request_bound_function_FP Task H H0 ts FP tsk Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.hep_workload_le_total_hep_rbf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (ts : List Task),
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
        Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
          ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk : Task) (j : Job),
            Prosa.Model.Task.Concept.job_of_task tsk j = true →
              ∀ (t : Prosa.Behavior.Time.instant) (Δ : ℕ),
                Prosa.Model.Aggregate.Workload.workload_of_hep_jobs arr_seq j t (t + Δ) ≤
                  Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_hep_workload_le_total_hep_rbf
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
       forall
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (tsk : Task) (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_13 Task
            inst_3
            inst_16 tsk j)
         Bool_true ->
       forall (t : Prosa_Behavior_Time_instant) (_UU0394_ : Nat),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job
            inst_13
            inst_20 arr_seq
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_13 Task
               inst_3
               inst_16 FP)
            j t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
               (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU0394_))
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
            inst_3
            inst_6
            inst_9 ts FP tsk _UU0394_)
```
