# `IBF_P_sol_le_IBF_NP`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_sol_le_IBF_NP`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_P_sol_le_IBF_NP`
- Certificate: `IBF_P_sol_le_IBF_NP_correspondence`

## Official Rocq

```coq
IBF_P_sol_le_IBF_NP :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {SBF : SupplyBoundFunction} (F Δ : duration),
is_true
  (F <=
   @task_cost Task H tsk +
   (fun F0 Δ0 : duration => F0 - @task_rtct Task H0 tsk + (Δ0 - SBF Δ0 - (F0 - SBF F0))) F Δ)

IBF_P_sol_le_IBF_NP is not universe polymorphic
Arguments IBF_P_sol_le_IBF_NP {Task H H0 Job H1 H3 H4} arr_seq ts%seq_scope tsk H_tsk_in_ts
  H_valid_run_to_completion_threshold {SBF} F Δ
IBF_P_sol_le_IBF_NP is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_sol_le_IBF_NP
Declared in library prosa.analysis.abstract.restricted_supply.abstract_rta, line 330, characters 8-27
@IBF_P_sol_le_IBF_NP
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobPreemptable Job)
         (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall (SBF : SupplyBoundFunction) (F Δ : duration),
       is_true (F <= @task_cost Task H tsk + (F - @task_rtct Task H0 tsk + (Δ - SBF Δ - (F - SBF F))))
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_P_sol_le_IBF_NP : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
      ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction) (F Δ : Prosa.Behavior.Time.duration),
        F ≤
          Prosa.Model.Task.Concept.task_cost tsk +
            (F - Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
              (Δ - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ -
                (F - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F)))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_IBF_P_sol_le_IBF_NP
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
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_23 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
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
         inst_20
         inst_23
         inst_13 arr_seq
         tsk ->
       forall (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction)
         (F _UU0394_ : Prosa_Behavior_Time_duration),
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat F
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_10 tsk)
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
               (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                  Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
                  (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                     inst_3
                     inst_13
                     tsk))
               (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                     Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                     _UU0394_
                     (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
                  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                     Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
                     (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F)))))
```
