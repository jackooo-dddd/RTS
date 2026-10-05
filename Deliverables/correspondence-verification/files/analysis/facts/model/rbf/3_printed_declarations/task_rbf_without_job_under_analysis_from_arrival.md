# `task_rbf_without_job_under_analysis_from_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis_from_arrival`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.task_rbf_without_job_under_analysis_from_arrival`
- Certificate: `task_rbf_without_job_under_analysis_from_arrival_correspondence`

## Official Rocq

```coq
task_rbf_without_job_under_analysis_from_arrival :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H1 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H0 tsk j) ->
@arrives_in Job arr_seq j ->
forall (t1 : instant) (Δ : duration),
is_true (@job_arrival Job H1 j < t1 + Δ) ->
is_true
  (@task_workload_between Task Job H0 H2 arr_seq tsk (@job_arrival Job H1 j) (t1 + Δ) - @job_cost Job H2 j <=
   @task_cost Task H tsk * @number_of_task_arrivals Job Task H0 arr_seq tsk (@job_arrival Job H1 j) (t1 + Δ) -
   @task_cost Task H tsk)

task_rbf_without_job_under_analysis_from_arrival is not universe polymorphic
Arguments task_rbf_without_job_under_analysis_from_arrival {Task H Job H0 H1 H2} 
  arr_seq H_arrival_times_are_consistent H_arrivals_have_valid_job_costs tsk j H_job_of_task 
  H_j_arrives_in t1 Δ H_job_arrival_lt
task_rbf_without_job_under_analysis_from_arrival is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis_from_arrival
Declared in library prosa.analysis.facts.model.rbf, line 725, characters 8-56
@task_rbf_without_job_under_analysis_from_arrival
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H1 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H0 tsk j) ->
       @arrives_in Job arr_seq j ->
       forall (t1 : instant) (Δ : duration),
       is_true (@job_arrival Job H1 j < t1 + Δ) ->
       is_true
         (@task_workload_between Task Job H0 H2 arr_seq tsk (@job_arrival Job H1 j) (t1 + Δ) -
          @job_cost Job H2 j <=
          @task_cost Task H tsk *
          @number_of_task_arrivals Job Task H0 arr_seq tsk (@job_arrival Job H1 j) (t1 + Δ) -
          @task_cost Task H tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.task_rbf_without_job_under_analysis_from_arrival : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (tsk : Task) (j : Job),
        Prosa.Model.Task.Concept.job_of_task tsk j = true →
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            ∀ (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration),
              Prosa.Behavior.Job.job_arrival j < t1 + Δ →
                Prosa.Model.Aggregate.Workload.task_workload_between arr_seq tsk (Prosa.Behavior.Job.job_arrival j)
                      (t1 + Δ) -
                    Prosa.Behavior.Job.job_cost j ≤
                  Prosa.Model.Task.Concept.task_cost tsk *
                      Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk (Prosa.Behavior.Job.job_arrival j)
                        (t1 + Δ) -
                    Prosa.Model.Task.Concept.task_cost tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_task_rbf_without_job_under_analysis_from_arrival
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_10
         inst_17 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_20 arr_seq ->
       forall (tsk : Task) (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_10 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j ->
       forall (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_10
            inst_17 j)
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_) ->
       LE_le_inst1 Nat instLENat
         (HSub_hSub_inst7 Nat Prosa_Behavior_Job_work Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Aggregate_Workload_task_workload_between Task
               inst_3 Job
               inst_10
               inst_13
               inst_20 arr_seq tsk
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_10
                  inst_17 j)
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_))
            (Prosa_Behavior_Job_JobCost_job_cost Job
               inst_10
               inst_20 j))
         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
            (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
               (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_6 tsk)
               (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
                  inst_10 Task
                  inst_3
                  inst_13 arr_seq tsk
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_10
                     inst_17 j)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     _UU0394_)))
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_6 tsk))
```
