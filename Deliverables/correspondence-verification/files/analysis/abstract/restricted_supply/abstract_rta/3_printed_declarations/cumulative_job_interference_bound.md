# `cumulative_job_interference_bound`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_rta.cumulative_job_interference_bound`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.cumulative_job_interference_bound`
- Certificate: `cumulative_job_interference_bound_correspondence`

## Official Rocq

```coq
cumulative_job_interference_bound :
forall {Task : TaskType} {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} 
  {H3 : JobCost Job} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job},
@work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
forall {SBF : SupplyBoundFunction},
@valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched tsk H5 H6 SBF ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H1 tsk j) ->
is_true (@job_cost_positive Job H3 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H2 H3 PState sched H5 H6 j t1 t2 ->
forall Δ : duration,
is_true (t1 + Δ < t2) ->
is_true (~~ @completed_by Job PState sched H3 j (t1 + Δ)) ->
is_true
  (@cumulative_interference Job H5 j t1 (t1 + Δ) <=
   Δ - SBF Δ + @cumul_intra_interference Job PState sched H5 j t1 (t1 + Δ))

cumulative_job_interference_bound is not universe polymorphic
Arguments cumulative_job_interference_bound {Task Job H1 H2 H3 PState} H_unit_supply_proc_model 
  arr_seq sched ts%seq_scope tsk H_tsk_in_ts {H5 H6} H_work_conserving {SBF} H_valid_SBF 
  j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval Δ H_inside_busy_interval
  H_job_j_is_not_completed
cumulative_job_interference_bound is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.abstract_rta.cumulative_job_interference_bound
Declared in library prosa.analysis.abstract.restricted_supply.abstract_rta, line 201, characters 14-47
@cumulative_job_interference_bound
     : forall (Task : TaskType) (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job)
         (H3 : JobCost Job) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (ts : seq (Equality.sort Task))
         (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job),
       @work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
       forall SBF : SupplyBoundFunction,
       @valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched tsk H5 H6 SBF ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H1 tsk j) ->
       is_true (@job_cost_positive Job H3 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H2 H3 PState sched H5 H6 j t1 t2 ->
       forall Δ : duration,
       is_true (t1 + Δ < t2) ->
       is_true (~~ @completed_by Job PState sched H3 j (t1 + Δ)) ->
       is_true
         (@cumulative_interference Job H5 j t1 (t1 + Δ) <=
          Δ - SBF Δ + @cumul_intra_interference Job PState sched H5 j t1 (t1 + Δ))
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.cumulative_job_interference_bound : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (ts : List Task) (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
          [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
          Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
            ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
              Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.valid_busy_sbf arr_seq sched tsk
                  Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                ∀ (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    Prosa.Model.Task.Concept.job_of_task tsk j = true →
                      Prosa.Model.Job.Properties.job_cost_positive j = true →
                        ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                          Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
                            ∀ (Δ : Prosa.Behavior.Time.duration),
                              t1 + Δ < t2 →
                                (!Prosa.Behavior.Service.completed_by sched j (t1 + Δ)) = true →
                                  Prosa.Analysis.Abstract.Definitions.cumulative_interference j t1 (t1 + Δ) ≤
                                    Δ - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ +
                                      Prosa.Analysis.Abstract.IBF.Supply.cumul_intra_interference sched j t1 (t1 + Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_cumulative_job_interference_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_7 PState ->
       forall
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
       forall
         (inst_49 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_52 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_49
         inst_52
         inst_14
         inst_17 PState
         arr_seq sched ->
       forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_valid_busy_sbf Task
         inst_3 Job
         inst_7
         inst_14
         inst_17
         inst_10 PState
         arr_seq sched tsk
         inst_49
         inst_52
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_17 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         inst_49
         inst_52
         inst_14
         inst_17 PState
         sched j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_7
               PState sched
               inst_17 j
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
            inst_7
            inst_49 j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
               Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_
               (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
            (Prosa_Analysis_Abstract_IBF_Supply_cumul_intra_interference Job
               inst_7
               PState sched
               inst_49 j
               t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_)))
```
