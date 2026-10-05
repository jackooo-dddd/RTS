# `IBF_P_bounds_interference`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_bounds_interference`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_P_bounds_interference`
- Certificate: `IBF_P_bounds_interference_correspondence`

## Official Rocq

```coq
IBF_P_bounds_interference :
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
forall intra_IBF : duration -> duration -> duration,
@intra_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6 intra_IBF ->
@job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6
  (fun A Δ : duration => Δ - SBF Δ + intra_IBF A Δ)
  (@relative_arrival_time_of_job_is_A Job H2 H3 PState sched H5 H6)

IBF_P_bounds_interference is not universe polymorphic
Arguments IBF_P_bounds_interference {Task Job H1 H2 H3 PState} H_unit_supply_proc_model 
  arr_seq sched ts%seq_scope tsk H_tsk_in_ts {H5 H6} H_work_conserving {SBF} H_valid_SBF
  intra_IBF%function_scope H_intra_supply_interference_is_bounded t1 t2 Δ j _ _ _ 
  _ _ X _
IBF_P_bounds_interference is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_bounds_interference
Declared in library prosa.analysis.abstract.restricted_supply.abstract_rta, line 267, characters 8-33
@IBF_P_bounds_interference
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
       forall intra_IBF : duration -> duration -> duration,
       @intra_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6 intra_IBF ->
       @job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6
         (fun A Δ : duration => Δ - SBF Δ + intra_IBF A Δ)
         (@relative_arrival_time_of_job_is_A Job H2 H3 PState sched H5 H6)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_P_bounds_interference : ∀
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
                ∀
                  (intra_IBF :
                    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                  Prosa.Analysis.Abstract.IBF.Supply.intra_interference_is_bounded_by arr_seq sched tsk intra_IBF →
                    Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk
                      (fun A Δ =>
                        Δ - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ + intra_IBF A Δ)
                      (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_IBF_P_bounds_interference
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
       forall
         intra_IBF : Prosa_Behavior_Time_duration ->
                     Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by Job
         inst_7 Task
         inst_3
         inst_10
         inst_14
         inst_17 PState
         arr_seq sched tsk
         inst_49
         inst_52 intra_IBF ->
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_7
         inst_49
         inst_52
         inst_14
         inst_17 PState
         arr_seq sched Task
         inst_3
         inst_10 tsk
         (fun A _UU0394_ : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
               Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_
               (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
            (intra_IBF A _UU0394_))
         (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job
            inst_7
            inst_14
            inst_17 PState
            sched inst_49
            inst_52)
```
