# `busy_intervals_are_bounded_rs_elf`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.bounded_bi.elf.busy_intervals_are_bounded_rs_elf`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Elf.busy_intervals_are_bounded_rs_elf`
- Certificate: `busy_intervals_are_bounded_rs_elf_correspondence`

## Official Rocq

```coq
busy_intervals_are_bounded_rs_elf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : PriorityPoint Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall FP : FP_policy Task,
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
@total_task_priorities Task FP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H2 arr_seq ->
forall (sched : @schedule Job PState) {JobReady0 : @JobReady Job PState H3 H2},
@work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched (@ELF Task H0 Job H2 H1 FP) ->
@valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
forall {H4 : JobPreemptable Job} {H5 : TaskMaxNonpreemptiveSegment Task},
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@valid_model_with_bounded_nonpreemptive_segments Task Job H1 H3 H5 H4 PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched
  (@ELF Task H0 Job H2 H1 FP) ->
@definitions.work_conserving Job H2 H3 PState arr_seq sched
  (@rs_jlfp_interference Task H0 Job H1 H2 PState FP arr_seq sched)
  (@rs_jlfp_interfering_workload Task H0 Job H1 H2 H3 PState FP arr_seq sched) ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall {H6 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H1 arr_seq H6 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall {SBF : SupplyBoundFunction},
@valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched (@ELF Task H0 Job H2 H1 FP) tsk SBF ->
unit_supply_bound_function SBF ->
forall L : duration,
is_true (0 < L) ->
(forall A : duration,
 is_true
   (@blocking_bound Task H H5 H0 ts H6 FP tsk A + @total_hep_request_bound_function_FP Task H H6 ts FP tsk L <=
    SBF L)) ->
@busy_intervals_are_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk
  (@rs_jlfp_interference Task H0 Job H1 H2 PState FP arr_seq sched)
  (@rs_jlfp_interfering_workload Task H0 Job H1 H2 H3 PState FP arr_seq sched) L

busy_intervals_are_bounded_rs_elf is not universe polymorphic
Arguments busy_intervals_are_bounded_rs_elf {Task H H0 Job H1 H2 H3 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model H_consumed_supply_proc_model FP H_priority_is_reflexive 
  H_priority_is_transitive H_total_priorities arr_seq H_valid_arrival_sequence sched 
  {JobReady0} H_job_ready H_sched_valid {H4 H5} H_valid_preemption_model
  H_valid_model_with_bounded_nonpreemptive_segments H_respects_policy H_work_conserving 
  ts%seq_scope H_all_jobs_from_taskset H_valid_job_cost {H6} H_is_arrival_curve tsk 
  H_tsk_in_ts {SBF} H_valid_SBF H_unit_SBF L H_L_positive H_fixed_point%function_scope 
  j _ _ _
busy_intervals_are_bounded_rs_elf is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.bounded_bi.elf.busy_intervals_are_bounded_rs_elf
Declared in library prosa.analysis.abstract.restricted_supply.bounded_bi.elf, line 291, characters 8-41
@busy_intervals_are_bounded_rs_elf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : PriorityPoint Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       @total_task_priorities Task FP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H2 arr_seq ->
       forall (sched : @schedule Job PState) (JobReady0 : @JobReady Job PState H3 H2),
       @work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched (@ELF Task H0 Job H2 H1 FP) ->
       @valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
       forall (H4 : JobPreemptable Job) (H5 : TaskMaxNonpreemptiveSegment Task),
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @valid_model_with_bounded_nonpreemptive_segments Task Job H1 H3 H5 H4 PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched
         (@ELF Task H0 Job H2 H1 FP) ->
       @definitions.work_conserving Job H2 H3 PState arr_seq sched
         (@rs_jlfp_interference Task H0 Job H1 H2 PState FP arr_seq sched)
         (@rs_jlfp_interfering_workload Task H0 Job H1 H2 H3 PState FP arr_seq sched) ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall H6 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H1 arr_seq H6 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall SBF : SupplyBoundFunction,
       @valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched (@ELF Task H0 Job H2 H1 FP) tsk SBF ->
       unit_supply_bound_function SBF ->
       forall L : duration,
       is_true (0 < L) ->
       (forall A : duration,
        is_true
          (@blocking_bound Task H H5 H0 ts H6 FP tsk A +
           @total_hep_request_bound_function_FP Task H H6 ts FP tsk L <= SBF L)) ->
       @busy_intervals_are_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk
         (@rs_jlfp_interference Task H0 Job H1 H2 PState FP arr_seq sched)
         (@rs_jlfp_interfering_workload Task H0 Job H1 H2 H3 PState FP arr_seq sched) L
New coercion path [GRing.subring_closedM; GRing.smulr_closedN] : GRing.subring_closed >-> GRing.oppr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedM] : GRing.subring_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedD] : GRing.subring_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.submod_closed_semi; GRing.subsemimod_closedD] : GRing.submod_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.subalg_closedBM; GRing.subring_closedB] : GRing.subalg_closed >-> GRing.zmod_closed is ambiguous with existing 
New coercion path [GRing.sdivr_closedM; GRing.smulr_closedM] : GRing.sdivr_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.divring_closed_div; GRing.sdivr_closedM] : GRing.divring_closed >-> GRing.smulr_closed is ambiguous with existing 
New coercion path [GRing.divalg_closedZ; GRing.subalg_closedBM] : GRing.divalg_closed >-> GRing.subring_closed is ambiguous with existing
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Elf.busy_intervals_are_bounded_rs_elf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] {Job : Prosa.Behavior.Job.JobType} [inst_3 : DecidableEq Job]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
          Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
            Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
              Prosa.Model.Priority.Definitions.total_task_priorities FP →
                ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
                  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
                    ∀ (sched : Prosa.Behavior.Schedule.schedule PState)
                      [inst_7 : Prosa.Behavior.Ready.JobReady Job PState],
                      Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                        Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                          ∀ [inst_8 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
                            [inst_9 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task],
                            Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                              Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments
                                  arr_seq sched →
                                Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq
                                    sched (Prosa.Model.Priority.Elf.ELF FP) →
                                  Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                                    ∀ (ts : List Task),
                                      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                                        Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                                          ∀ [inst_10 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                                            Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                                              ∀ (tsk : Task),
                                                decide (tsk ∈ ts) = true →
                                                  ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
                                                    Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf arr_seq sched tsk
                                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                      Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
                                                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                        ∀ (L : Prosa.Behavior.Time.duration),
                                                          0 < L →
                                                            (∀ (A : Prosa.Behavior.Time.duration),
                                                                Prosa.Analysis.Definitions.BlockingBound.Elf.blocking_bound
                                                                      ts tsk A +
                                                                    Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP
                                                                      ts tsk L ≤
                                                                  Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                                                    L) →
                                                              Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by
                                                                arr_seq sched tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Elf_busy_intervals_are_bounded_rs_elf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_13),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_13 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_13 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_13 PState ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3 FP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_13,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_20 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_13
                    PState)
         (inst_65 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_13
            PState
            inst_23
            inst_20),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_13
         inst_20
         inst_23 PState
         inst_65 arr_seq
         sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_9 Job
            inst_13
            inst_20
            inst_16 FP) ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_13
         inst_20 PState
         sched inst_23
         inst_65 arr_seq ->
       forall
         (inst_86 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_13)
         (inst_89 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3),
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_13
         inst_23
         inst_86 PState
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_3 Job
         inst_13
         inst_16
         inst_23
         inst_89
         inst_86 PState
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_13
         inst_20
         inst_23 PState
         inst_86
         inst_65 arr_seq
         sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_9 Job
            inst_13
            inst_20
            inst_16 FP) ->
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_13
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_13
            PState arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_9
               Job
               inst_13
               inst_20
               inst_16
               FP))
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_13
            inst_23
            PState arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_9
               Job
               inst_13
               inst_20
               inst_16
               FP))
         inst_20
         inst_23 PState
         arr_seq sched ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_13
         inst_16 arr_seq
         ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_23 arr_seq ->
       forall
         inst_156 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_13
         inst_16 arr_seq
         inst_156 ts ->
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
       forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf Task
         inst_3 Job
         inst_13
         inst_20
         inst_23
         inst_16 PState
         arr_seq sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_9 Job
            inst_13
            inst_20
            inst_16 FP)
         tsk (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       (forall A : Prosa_Behavior_Time_duration,
        LE_le_inst1 Nat instLENat
          (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
             (Prosa_Analysis_Definitions_BlockingBound_Elf_blocking_bound Task
                inst_3
                inst_6
                inst_89
                inst_9
                ts
                inst_156
                FP tsk A)
             (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
                inst_3
                inst_6
                inst_156
                ts FP tsk L))
          (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF L)) ->
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_13
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_13
            PState arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_9
               Job
               inst_13
               inst_20
               inst_16
               FP))
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_13
            inst_23
            PState arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_9
               Job
               inst_13
               inst_20
               inst_16
               FP))
         inst_20
         inst_23 PState
         arr_seq sched Task
         inst_3
         inst_16 tsk L
```
