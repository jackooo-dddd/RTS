# `soln_abstract_response_time_recurrence`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.soln_abstract_response_time_recurrence`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.FifoFixpoint.soln_abstract_response_time_recurrence`
- Certificate: `soln_abstract_response_time_recurrence_correspondence`

## Official Rocq

```coq
soln_abstract_response_time_recurrence :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : TaskRunToCompletionThreshold Task}
  {Job : JobType} {H3 : JobTask Job Task} {H4 : JobCost Job} {H5 : JobArrival Job} 
  {H6 : JobPreemptable Job} {PState : ProcessorState Job} {SBF : SupplyBoundFunction},
sbf_is_monotone SBF ->
unit_supply_bound_function SBF ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall arr_seq : arrival_sequence Job,
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall sched : @schedule Job PState,
@valid_busy_sbf Task Job H5 H4 H3 PState arr_seq sched (@FIFO Job H5) tsk SBF ->
@valid_task_run_to_completion_threshold Task H Job H3 H4 H6 H1 arr_seq tsk ->
forall L : duration,
is_true (0 < L) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H0 tsk 1) ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_search_space Task H ts H0 L A) ->
 exists F : duration,
   is_true (@total_request_bound_function Task H H0 ts (A + 1) <= SBF F) /\ is_true (F <= A + R)) ->
forall A : duration,
search_space.is_in_search_space L (@fifo.IBF SBF Task H ts H0 tsk) A ->
exists F : duration,
  is_true (F <= A + R) /\
  is_true (@task_rtct Task H1 tsk + @fifo_fixpoint.intra_IBF Task H H0 ts tsk A F <= SBF F) /\
  is_true (SBF F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= SBF (A + R))

soln_abstract_response_time_recurrence is not universe polymorphic
Arguments soln_abstract_response_time_recurrence {Task H H0 H1 Job H3 H4 H5 H6 PState SBF} 
  H_SBF_monotone H_unit_SBF ts%seq_scope tsk H_tsk_in_ts arr_seq H_valid_arrival_curve 
  sched H_valid_SBF H_valid_run_to_completion_threshold L H_L_positive H_task_cost_pos 
  H_arrival_curve_pos R H_R_is_maximum%function_scope A _
soln_abstract_response_time_recurrence is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.soln_abstract_response_time_recurrence
Declared in
library prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint, line 113, characters 8-46
@soln_abstract_response_time_recurrence
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task)
         (H1 : TaskRunToCompletionThreshold Task) (Job : JobType) (H3 : JobTask Job Task) 
         (H4 : JobCost Job) (H5 : JobArrival Job) (H6 : JobPreemptable Job) (PState : ProcessorState Job)
         (SBF : SupplyBoundFunction),
       sbf_is_monotone SBF ->
       unit_supply_bound_function SBF ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall arr_seq : arrival_sequence Job,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall sched : @schedule Job PState,
       @valid_busy_sbf Task Job H5 H4 H3 PState arr_seq sched (@FIFO Job H5) tsk SBF ->
       @valid_task_run_to_completion_threshold Task H Job H3 H4 H6 H1 arr_seq tsk ->
       forall L : duration,
       is_true (0 < L) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H0 tsk 1) ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_search_space Task H ts H0 L A) ->
        exists F : duration,
          is_true (@total_request_bound_function Task H H0 ts (A + 1) <= SBF F) /\ is_true (F <= A + R)) ->
       forall A : duration,
       search_space.is_in_search_space L (@fifo.IBF SBF Task H ts H0 tsk) A ->
       exists F : duration,
         is_true (F <= A + R) /\
         is_true (@task_rtct Task H1 tsk + @fifo_fixpoint.intra_IBF Task H H0 ts tsk A F <= SBF F) /\
         is_true (SBF F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= SBF (A + R))
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.FifoFixpoint.soln_abstract_response_time_recurrence : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Behavior.Job.JobArrival Job]
  [inst_8 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
  Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone
      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
    Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
      ∀ (ts : List Task) (tsk : Task),
        decide (tsk ∈ ts) = true →
          ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
            Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                Prosa.Model.Task.Arrival.Curves.max_arrivals →
              ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf arr_seq sched tsk
                    Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                  Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                    ∀ (L : Prosa.Behavior.Time.duration),
                      0 < L →
                        0 < Prosa.Model.Task.Concept.task_cost tsk →
                          0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                            ∀ (R : Prosa.Behavior.Time.duration),
                              (∀ (A : Prosa.Behavior.Time.duration),
                                  Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.is_in_search_space ts L A =
                                      true →
                                    ∃ F,
                                      Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts
                                            (A + 1) ≤
                                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F ∧
                                        F ≤ A + R) →
                                ∀ (A : Prosa.Behavior.Time.duration),
                                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                                      (fun A0 F =>
                                        F - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F +
                                          (Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function
                                              ts (A0 + 1) -
                                            Prosa.Model.Task.Concept.task_cost tsk))
                                      A →
                                    ∃ F ≤ A + R,
                                      Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                                            (Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function
                                                ts (A + 1) -
                                              Prosa.Model.Task.Concept.task_cost tsk) ≤
                                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F ∧
                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F +
                                            (Prosa.Model.Task.Concept.task_cost tsk -
                                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                            (A + R)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_FifoFixpoint_soln_abstract_response_time_recurrence
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : 
          DecidableEq Job)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_16
            Task
            inst_3)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_16)
         (inst_26 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_16)
         (inst_29 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_16)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_16)
         (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction),
       Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_16,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3
         ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9) ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_16
                   PState,
       Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf Task
         inst_3
         Job
         inst_16
         inst_26
         inst_23
         inst_19
         PState arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_16
            inst_26)
         tsk (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_6
         Job
         inst_16
         inst_19
         inst_23
         inst_29
         inst_12
         arr_seq tsk ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_6
            tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9
            tsk (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fifo_is_in_search_space Task
             inst_3
             inst_6
             ts
             inst_9
             L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Nat instLENat
                (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
                   inst_3
                   inst_6
                   inst_9
                   ts
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                      (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat F
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))) ->
       forall A : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 F : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
               Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
               (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
                  inst_3
                  inst_6
                  inst_9
                  ts
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_6
                  tsk)))
         A ->
       Exists Prosa_Behavior_Time_duration
         (fun F : Prosa_Behavior_Time_duration =>
          And
            (LE_le_inst1 Prosa_Behavior_Time_duration instLENat F
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R))
            (And
               (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                  (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
                     (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                        inst_3
                        inst_12
                        tsk)
                     (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                        (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
                           inst_3
                           inst_6
                           inst_9
                           ts
                           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                              Prosa_Behavior_Time_duration
                              (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                           inst_3
                           inst_6
                           tsk)))
                  (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
               (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                  (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
                     Prosa_Behavior_Job_work (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                     (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F)
                     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                        Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                           inst_3
                           inst_6
                           tsk)
                        (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                           inst_3
                           inst_12
                           tsk)))
                  (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                        A R)))))
```
