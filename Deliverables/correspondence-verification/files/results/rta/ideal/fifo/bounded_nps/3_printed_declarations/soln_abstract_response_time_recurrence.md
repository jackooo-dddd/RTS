# `soln_abstract_response_time_recurrence`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.soln_abstract_response_time_recurrence`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.soln_abstract_response_time_recurrence`
- Certificate: `soln_abstract_response_time_recurrence_correspondence`

## Official Rocq

```coq
soln_abstract_response_time_recurrence :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : TaskRunToCompletionThreshold Task}
  {Job : JobType} {H2 : JobTask Job Task} {H4 : JobCost Job} {H5 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@valid_task_run_to_completion_threshold Task H Job H2 H4 H5 H1 arr_seq tsk ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H0 ts L ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_concrete_search_space Task H H0 ts L A) ->
 exists F : nat,
   is_true (\sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A + 1) <= A + F) /\
   is_true (F <= R)) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H0 tsk 1) ->
forall A : nat,
       (fun A1 : duration =>
        fun=> \sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A1 + 1) - @task_cost Task H tsk)]
  A ->
exists F : nat,
  is_true
    (@task_rtct Task H1 tsk +
     (fun A0 : duration =>
      fun=> \sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A0 + 1) - @task_cost Task H tsk) A
       (A + F) <=
     A + F) /\
  is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)

soln_abstract_response_time_recurrence is not universe polymorphic
Arguments soln_abstract_response_time_recurrence {Task H H0 H1 Job H2 H4 H5} arr_seq 
  ts%seq_scope H_valid_arrival_curve tsk H_tsk_in_ts H_valid_run_to_completion_threshold 
  L H_L_positive H_fixed_point R H_R_max%function_scope H_task_cost_pos H_arrival_curve_pos 
  A%nat_scope _
soln_abstract_response_time_recurrence is opaque
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.soln_abstract_response_time_recurrence
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 409, characters 10-48
@soln_abstract_response_time_recurrence
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task)
         (H1 : TaskRunToCompletionThreshold Task) (Job : JobType) (H2 : JobTask Job Task) 
         (H4 : JobCost Job) (H5 : JobPreemptable Job) (arr_seq : arrival_sequence Job)
         (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @valid_task_run_to_completion_threshold Task H Job H2 H4 H5 H1 arr_seq tsk ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H0 ts L ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_concrete_search_space Task H H0 ts L A) ->
        exists F : nat,
          is_true (\sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A + 1) <= A + F) /\
          is_true (F <= R)) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H0 tsk 1) ->
       forall A : nat,
       is_in_search_space L
         (fun A0 : duration =>
          fun=> \sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A0 + 1) -
                @task_cost Task H tsk)
         A ->
       exists F : nat,
         is_true
           (@task_rtct Task H1 tsk +
            (\sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A + 1) - @task_cost Task H tsk) <=
            A + F) /\
         is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.soln_abstract_response_time_recurrence : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
          ∀ (L : Prosa.Behavior.Time.duration),
            0 < L →
              L = Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L →
                ∀ (R : Prosa.Behavior.Time.duration),
                  (∀ (A : Prosa.Behavior.Time.duration),
                      Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space ts L A = true →
                        ∃ F,
                          (Prosa.Util.Sum.sumSeq ts fun tsko =>
                                Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
                                  (A + 1)) ≤
                              A + F ∧
                            F ≤ R) →
                    0 < Prosa.Model.Task.Concept.task_cost tsk →
                      0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                        ∀ (A : ℕ),
                          Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                              (fun A0 x =>
                                (Prosa.Util.Sum.sumSeq ts fun tsko =>
                                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
                                      (A0 + 1)) -
                                  Prosa.Model.Task.Concept.task_cost tsk)
                              A →
                            ∃ F,
                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                                    ((Prosa.Util.Sum.sumSeq ts fun tsko =>
                                        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
                                          (A + 1)) -
                                      Prosa.Model.Task.Concept.task_cost tsk) ≤
                                  A + F ∧
                                F +
                                    (Prosa.Model.Task.Concept.task_cost tsk -
                                      Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                  R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_soln_abstract_response_time_recurrence
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
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
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13) ->
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
         inst_16 arr_seq tsk ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_13 ts L) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space Task
             inst_3
             inst_10
             inst_13 ts L A)
          Bool_true ->
        Exists Nat
          (fun F : Nat =>
           And
             (LE_le_inst1 Nat instLENat
                (Prosa_Util_Sum_sumSeq Task ts
                   (fun tsko : Task =>
                    Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                      inst_3
                      inst_10
                      inst_13 tsko
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                   (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
             (LE_le_inst1 Nat instLENat F R))) ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 _ : Prosa_Behavior_Time_duration =>
          HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Util_Sum_sumSeq Task ts
               (fun tsko : Task =>
                Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_13 tsko
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_10 tsk))
         A ->
       Exists Nat
         (fun F : Nat =>
          And
            (LE_le_inst1 Prosa_Behavior_Job_work instLENat
               (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
                  (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                  (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                     inst_3
                     inst_16 tsk)
                  (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                     (Prosa_Util_Sum_sumSeq Task ts
                        (fun tsko : Task =>
                         Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                           inst_3
                           inst_10
                           inst_13 tsko
                           (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat
                              (instHAdd_inst1 Nat instAddNat) A
                              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
                     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                        inst_3
                        inst_10 tsk)))
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
                        inst_16 tsk)))
               R))
```
