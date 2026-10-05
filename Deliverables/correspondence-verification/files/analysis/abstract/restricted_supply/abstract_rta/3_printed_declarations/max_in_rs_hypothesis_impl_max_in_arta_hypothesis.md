# `max_in_rs_hypothesis_impl_max_in_arta_hypothesis`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_rta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis`
- Certificate: `max_in_rs_hypothesis_impl_max_in_arta_hypothesis_correspondence`

## Official Rocq

```coq
max_in_rs_hypothesis_impl_max_in_arta_hypothesis :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} 
  {H4 : JobPreemptable Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job} (L : duration) {SBF : SupplyBoundFunction},
@valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched tsk H5 H6 SBF ->
unit_supply_bound_function SBF ->
forall (intra_IBF : duration -> duration -> duration) (R : duration),
(forall A : duration,
 is_in_search_space L (fun A0 Δ : duration => Δ - SBF Δ + intra_IBF A0 Δ) A ->
 exists F : duration,
   is_true (F <= A + R) /\
   is_true (@task_rtct Task H0 tsk + intra_IBF A F <= SBF F) /\
   is_true (SBF F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= SBF (A + R))) ->
forall A : duration,
is_in_search_space L (fun A0 Δ : duration => Δ - SBF Δ + intra_IBF A0 Δ) A ->
exists F : duration,
  is_true (@task_rtct Task H0 tsk + (F - SBF F + intra_IBF A F) <= F) /\
  is_true
    (@task_cost Task H tsk + (F - @task_rtct Task H0 tsk + (A + R - SBF (A + R) - (F - SBF F))) <= A + R)

max_in_rs_hypothesis_impl_max_in_arta_hypothesis is not universe polymorphic
Arguments max_in_rs_hypothesis_impl_max_in_arta_hypothesis {Task H H0 Job H1 H2 H3 H4 PState} 
  arr_seq sched ts%seq_scope tsk H_tsk_in_ts H_valid_run_to_completion_threshold 
  {H5 H6} L {SBF} H_valid_SBF H_unit_SBF intra_IBF%function_scope R H_R_is_maximum_rs%function_scope 
  A _
max_in_rs_hypothesis_impl_max_in_arta_hypothesis is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.abstract_rta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis
Declared in library prosa.analysis.abstract.restricted_supply.abstract_rta, line 343, characters 8-56
@max_in_rs_hypothesis_impl_max_in_arta_hypothesis
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job)
         (H4 : JobPreemptable Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job) (L : duration)
         (SBF : SupplyBoundFunction),
       @valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched tsk H5 H6 SBF ->
       unit_supply_bound_function SBF ->
       forall (intra_IBF : duration -> duration -> duration) (R : duration),
       (forall A : duration,
        is_in_search_space L (fun A0 Δ : duration => Δ - SBF Δ + intra_IBF A0 Δ) A ->
        exists F : duration,
          is_true (F <= A + R) /\
          is_true (@task_rtct Task H0 tsk + intra_IBF A F <= SBF F) /\
          is_true (SBF F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= SBF (A + R))) ->
       forall A : duration,
       is_in_search_space L (fun A0 Δ : duration => Δ - SBF Δ + intra_IBF A0 Δ) A ->
       exists F : duration,
         is_true (@task_rtct Task H0 tsk + (F - SBF F + intra_IBF A F) <= F) /\
         is_true
           (@task_cost Task H tsk + (F - @task_rtct Task H0 tsk + (A + R - SBF (A + R) - (F - SBF F))) <=
            A + R)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
      ∀ [inst_8 : Prosa.Analysis.Abstract.Definitions.Interference Job]
        [inst_9 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] (L : Prosa.Behavior.Time.duration)
        (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
        Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.valid_busy_sbf arr_seq sched tsk
            Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
          Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
              Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
            ∀ (intra_IBF : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration)
              (R : Prosa.Behavior.Time.duration),
              (∀ (A : Prosa.Behavior.Time.duration),
                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                      (fun A0 Δ =>
                        Δ - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ + intra_IBF A0 Δ)
                      A →
                    ∃ F ≤ A + R,
                      Prosa.Model.Task.Preemption.Parameters.task_rtct tsk + intra_IBF A F ≤
                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F ∧
                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F +
                            (Prosa.Model.Task.Concept.task_cost tsk -
                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function (A + R)) →
                ∀ (A : Prosa.Behavior.Time.duration),
                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                      (fun A0 Δ =>
                        Δ - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ + intra_IBF A0 Δ)
                      A →
                    ∃ F,
                      Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                            (F - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F +
                              intra_IBF A F) ≤
                          F ∧
                        Prosa.Model.Task.Concept.task_cost tsk +
                            (F - Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                              (A + R -
                                  Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function (A + R) -
                                (F - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F))) ≤
                          A + R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_max_in_rs_hypothesis_impl_max_in_arta_hypothesis
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
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
         (inst_26 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7
                    PState)
         (ts : List Task) (tsk : Task),
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
         inst_16
         inst_23
         inst_26
         inst_13 arr_seq tsk ->
       forall
         (inst_57 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_60 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7)
         (L : Prosa_Behavior_Time_duration) (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction),
       Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_valid_busy_sbf Task
         inst_3 Job
         inst_7
         inst_20
         inst_23
         inst_16 PState
         arr_seq sched tsk
         inst_57
         inst_60
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall
         (intra_IBF : Prosa_Behavior_Time_duration ->
                      Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
         (R : Prosa_Behavior_Time_duration),
       (forall A : Prosa_Behavior_Time_duration,
        Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
          (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
           HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
             Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
             (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                _UU0394_
                (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
             (intra_IBF A0 _UU0394_))
          A ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat F
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R))
             (And
                (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                   (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
                      Prosa_Behavior_Job_work (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                      (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                         inst_3
                         inst_13
                         tsk)
                      (intra_IBF A F))
                   (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
                (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                   (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
                      Prosa_Behavior_Job_work (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                      (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F)
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
                   (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))))) ->
       forall A : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
               Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_
               (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
            (intra_IBF A0 _UU0394_))
         A ->
       Exists Prosa_Behavior_Time_duration
         (fun F : Prosa_Behavior_Time_duration =>
          And
            (LE_le_inst1 Prosa_Behavior_Job_work instLENat
               (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                  (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                  (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                     inst_3
                     inst_13
                     tsk)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                        Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                        F (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
                     (intra_IBF A F)))
               F)
            (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                  (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                     inst_3
                     inst_10
                     tsk)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                        Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                        F
                        (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                           inst_3
                           inst_13
                           tsk))
                     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                        (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                           Prosa_Behavior_Time_duration
                           (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                              Prosa_Behavior_Time_duration
                              (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)
                           (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF
                              (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                                 Prosa_Behavior_Time_duration
                                 (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))
                        (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                           Prosa_Behavior_Time_duration
                           (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
                           (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F)))))
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))
```
