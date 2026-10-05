# `self_intf_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound`
- Lean: `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.self_intf_bound`
- Certificate: `self_intf_bound_correspondence`

## Official Rocq

```coq
self_intf_bound :
forall {Task : TaskType} {H : TaskCost Task} {MaxArrivals0 : MaxArrivals Task} {Job : JobType}
  {H1 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
@arrivals_have_valid_job_costs Task H Job H1 Cost arr_seq ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
forall ts : seq (Equality.sort Task),
@taskset_respects_max_arrivals Task Job H1 arr_seq MaxArrivals0 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall priority_inversion_bound L : duration,
is_true (0 < L) ->
L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
forall (t1 : instant) (Δ : duration) (j : Equality.sort Job),
is_true (@job_cost_positive Job Cost j) ->
is_true (@job_of_task Job Task H1 tsk j) ->
@arrives_in Job arr_seq j ->
is_true (t1 <= @job_arrival Job Arrival j) ->
is_true
  (@workload_of_jobs Job Cost ((@another_hep_job_of_same_task Task Job H1 (@FP_to_JLFP Job Task H1 FP))^~ j)
     (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
   @task_request_bound_function Task H MaxArrivals0 tsk (maxn (@job_arrival Job Arrival j - t1 + 1) Δ) -
   @task_cost Task H tsk)

self_intf_bound is not universe polymorphic
Arguments self_intf_bound {Task H MaxArrivals0 Job H1 Arrival Cost} arr_seq H_valid_arrival_sequence
  H_valid_job_cost {FP} H_priority_is_reflexive ts%seq_scope H_is_arrival_curve tsk 
  H_tsk_in_ts priority_inversion_bound L H_L_positive H_fixed_point t1 Δ j H_job_cost_positive 
  H_job_of_task H_j_in_arr_seq H_t1_le_job_arrival
self_intf_bound is opaque
Expands to: Constant prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound
Declared in library prosa.results.rta.ideal.fp.nonseq.bounded_pi, line 258, characters 10-25
@self_intf_bound
     : forall (Task : TaskType) (H : TaskCost Task) (MaxArrivals0 : MaxArrivals Task) 
         (Job : JobType) (H1 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H1 Cost arr_seq ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       forall ts : seq (Equality.sort Task),
       @taskset_respects_max_arrivals Task Job H1 arr_seq MaxArrivals0 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall priority_inversion_bound L : duration,
       is_true (0 < L) ->
       L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
       forall (t1 : instant) (Δ : duration) (j : Equality.sort Job),
       is_true (@job_cost_positive Job Cost j) ->
       is_true (@job_of_task Job Task H1 tsk j) ->
       @arrives_in Job arr_seq j ->
       is_true (t1 <= @job_arrival Job Arrival j) ->
       is_true
         (@workload_of_jobs Job Cost
            ((@another_hep_job_of_same_task Task Job H1 (@FP_to_JLFP Job Task H1 FP))^~ j)
            (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
          @task_request_bound_function Task H MaxArrivals0 tsk (maxn (@job_arrival Job Arrival j - t1 + 1) Δ) -
          @task_cost Task H tsk)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.self_intf_bound : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
        Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
          ∀ (ts : List Task),
            Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
              ∀ (tsk : Task),
                decide (tsk ∈ ts) = true →
                  ∀ (priority_inversion_bound L : Prosa.Behavior.Time.duration),
                    0 < L →
                      L =
                          priority_inversion_bound +
                            Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk
                              L →
                        ∀ (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration) (j : Job),
                          Prosa.Model.Job.Properties.job_cost_positive j = true →
                            Prosa.Model.Task.Concept.job_of_task tsk j = true →
                              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                t1 ≤ Prosa.Behavior.Job.job_arrival j →
                                  Prosa.Model.Aggregate.Workload.workload_of_jobs
                                      (fun x => Prosa.Model.Priority.Definitions.another_hep_job_of_same_task x j)
                                      (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) ≤
                                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk
                                        (Nat.max (Prosa.Behavior.Job.job_arrival j - t1 + 1) Δ) -
                                      Prosa.Model.Task.Concept.task_cost tsk
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_self_intf_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_20 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23 arr_seq ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       forall ts : List Task,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16 arr_seq
         inst_13 ts ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall priority_inversion_bound L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_10
               inst_13 ts FP tsk L)) ->
       forall (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration) (j : Job),
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_23 j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_16 tsk j)
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_7
            inst_20 j) ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_23
            (fun x : Job =>
             Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task
               inst_3 Job
               inst_7
               inst_16
               (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
                  inst_7 Task
                  inst_3
                  inst_16 FP)
               x j)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_)))
         (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
               inst_3
               inst_10
               inst_13 tsk
               (Nat_max
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                        Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_7
                           inst_20
                           j)
                        t1)
                     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                  _UU0394_))
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_10 tsk))
```
