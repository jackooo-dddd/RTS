# `correct_search_space`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.rta.ideal.fp.nonseq.bounded_pi.correct_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.correct_search_space`
- Certificate: `correct_search_space_correspondence`

## Official Rocq

```coq
correct_search_space :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task}
  {MaxArrivals0 : MaxArrivals Task} {Job : JobType} {H1 : JobTask Job Task} {Cost : JobCost Job}
  {JobPreemptable0 : JobPreemptable Job} (arr_seq : arrival_sequence Job) {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
forall ts : seq (Equality.sort Task),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task MaxArrivals0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@valid_task_run_to_completion_threshold Task H Job H1 Cost JobPreemptable0 H0 arr_seq tsk ->
forall priority_inversion_bound L : duration,
is_true (0 < L) ->
L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_concrete_search_space Task H MaxArrivals0 tsk L A) ->
 exists F : duration,
   is_true (0 < F) /\
   is_true
     (priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk (A + F) -
      (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task MaxArrivals0 tsk 1) ->
forall A : nat,
exists F : nat,
  is_true
    (@task_rtct Task H0 tsk + @IBF Task H MaxArrivals0 FP ts tsk priority_inversion_bound A (A + F) <= A + F) /\
  is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)

correct_search_space is not universe polymorphic
Arguments correct_search_space {Task H H0 MaxArrivals0 Job H1 Cost JobPreemptable0} 
  arr_seq {FP} H_priority_is_reflexive ts%seq_scope H_valid_arrival_curve tsk H_tsk_in_ts
  H_valid_run_to_completion_threshold priority_inversion_bound L H_L_positive H_fixed_point 
  R H_R_is_maximum%function_scope H_task_cost_pos H_arrival_curve_pos A%nat_scope 
  _
correct_search_space is opaque
Expands to: Constant prosa.results.rta.ideal.fp.nonseq.bounded_pi.correct_search_space
Declared in library prosa.results.rta.ideal.fp.nonseq.bounded_pi, line 389, characters 14-34
@correct_search_space
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task)
         (MaxArrivals0 : MaxArrivals Task) (Job : JobType) (H1 : JobTask Job Task) 
         (Cost : JobCost Job) (JobPreemptable0 : JobPreemptable Job) (arr_seq : arrival_sequence Job)
         (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       forall ts : seq (Equality.sort Task),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task MaxArrivals0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @valid_task_run_to_completion_threshold Task H Job H1 Cost JobPreemptable0 H0 arr_seq tsk ->
       forall priority_inversion_bound L : duration,
       is_true (0 < L) ->
       L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_concrete_search_space Task H MaxArrivals0 tsk L A) ->
        exists F : duration,
          is_true (0 < F) /\
          is_true
            (priority_inversion_bound +
             @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk (A + F) -
             (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task MaxArrivals0 tsk 1) ->
       forall A : nat,
       is_in_search_space L (@IBF Task H MaxArrivals0 FP ts tsk priority_inversion_bound) A ->
       exists F : nat,
         is_true
           (@task_rtct Task H0 tsk + @IBF Task H MaxArrivals0 FP ts tsk priority_inversion_bound A (A + F) <=
            A + F) /\
         is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.correct_search_space : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    ∀ (ts : List Task),
      Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
        ∀ (tsk : Task),
          decide (tsk ∈ ts) = true →
            Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
              ∀ (priority_inversion_bound L : Prosa.Behavior.Time.duration),
                0 < L →
                  L =
                      priority_inversion_bound +
                        Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk L →
                    ∀ (R : Prosa.Behavior.Time.duration),
                      (∀ (A : Prosa.Behavior.Time.duration),
                          Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.is_in_concrete_search_space tsk L A = true →
                            ∃ F,
                              0 < F ∧
                                priority_inversion_bound +
                                        Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP
                                          ts tsk (A + F) -
                                      (Prosa.Model.Task.Concept.task_cost tsk -
                                        Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                    A + F ∧
                                  F +
                                      (Prosa.Model.Task.Concept.task_cost tsk -
                                        Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                    R) →
                        0 < Prosa.Model.Task.Concept.task_cost tsk →
                          0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                            ∀ (A : ℕ),
                              Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                                  (Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF ts tsk priority_inversion_bound) A →
                                ∃ F,
                                  Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                                        Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF ts tsk priority_inversion_bound
                                          A (A + F) ≤
                                      A + F ∧
                                    F +
                                        (Prosa.Model.Task.Concept.task_cost tsk -
                                          Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                      R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_correct_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_26 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       forall ts : List Task,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_16) ->
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
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_19
         inst_23
         inst_26
         inst_13 arr_seq tsk ->
       forall priority_inversion_bound L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_10
               inst_16 ts FP tsk L)) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_is_in_concrete_search_space Task
             inst_3
             inst_10
             inst_16 tsk L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
                (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) F)
             (And
                (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                   (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
                         (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP
                            Task
                            inst_3
                            inst_10
                            inst_16
                            ts FP tsk
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
                      (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                         Prosa_Behavior_Time_duration
                         (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                            inst_3
                            inst_10
                            tsk)
                         (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                            inst_3
                            inst_13
                            tsk)))
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                      F))
                (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) F
                      (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                         Prosa_Behavior_Time_duration
                         (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                            inst_3
                            inst_10
                            tsk)
                         (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                            inst_3
                            inst_13
                            tsk)))
                   R)))) ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_16 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_IBF Task
            inst_3
            inst_10
            inst_16 FP ts tsk
            priority_inversion_bound)
         A ->
       Exists Nat
         (fun F : Nat =>
          And
            (LE_le_inst1 Prosa_Behavior_Job_work instLENat
               (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
                  (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                  (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                     inst_3
                     inst_13 tsk)
                  (Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_IBF Task
                     inst_3
                     inst_10
                     inst_16 FP ts
                     tsk priority_inversion_bound A
                     (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A F)))
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A F))
            (LE_le_inst1 Nat instLENat
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) F
                  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                     Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                        inst_3
                        inst_10 tsk)
                     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                        inst_3
                        inst_13 tsk)))
               R))
```
