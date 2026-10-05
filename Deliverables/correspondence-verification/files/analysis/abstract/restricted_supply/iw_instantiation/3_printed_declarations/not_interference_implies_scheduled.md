# `not_interference_implies_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_instantiation.not_interference_implies_scheduled`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.not_interference_implies_scheduled`
- Certificate: `not_interference_implies_scheduled_correspondence`

## Official Rocq

```coq
not_interference_implies_scheduled :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_cost Job H2 j) ->
forall t1 t2 : instant,
@definitions.busy_interval_prefix Job H1 H2 PState sched
  (@rs_jlfp_interference Job PState arr_seq sched JLFP)
  (@rs_jlfp_interfering_workload Job H2 PState arr_seq sched JLFP) j t1 t2 ->
forall t : instant,
is_true (t1 <= t < t2) ->
is_true (~~ @interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP) j t) ->
is_true (@receives_service_at Job PState sched j t)

not_interference_implies_scheduled is not universe polymorphic
Arguments not_interference_implies_scheduled {Job H1 H2 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model H_consumed_supply_proc_model arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  {JLFP} H_priority_is_reflexive {JobReady0} H_work_bearing_readiness H_sched_valid 
  H_work_conserving j H_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix 
  t H_t_in_busy_interval _
not_interference_implies_scheduled is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_instantiation.not_interference_implies_scheduled
Declared in library prosa.analysis.abstract.restricted_supply.iw_instantiation, line 469, characters 12-46
@not_interference_implies_scheduled
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall JobReady0 : @JobReady Job PState H2 H1,
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (0 < @job_cost Job H2 j) ->
       forall t1 t2 : instant,
       @definitions.busy_interval_prefix Job H1 H2 PState sched
         (@rs_jlfp_interference Job PState arr_seq sched JLFP)
         (@rs_jlfp_interfering_workload Job H2 PState arr_seq sched JLFP) j t1 t2 ->
       forall t : instant,
       is_true (t1 <= t < t2) ->
       is_true (~~ @interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP) j t) ->
       is_true (@receives_service_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.not_interference_implies_scheduled : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
          Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
            ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
              Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
                Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                    ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
                      Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                        ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job PState],
                          Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                                ∀ (j : Job),
                                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                    0 < Prosa.Behavior.Job.job_cost j →
                                      ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                        Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
                                          ∀ (t : Prosa.Behavior.Time.instant),
                                            (decide (t1 ≤ t) && decide (t < t2)) = true →
                                              (!Prosa.Analysis.Abstract.Definitions.interference j t) = true →
                                                Prosa.Behavior.Service.receives_service_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_not_interference_implies_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10
         arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_10
         PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState
         sched inst_13 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall
         JobReady0 : Prosa_Behavior_Ready_JobReady Job
                       inst_7
                       PState
                       inst_13
                       inst_10,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_7
         inst_10
         inst_13
         PState JobReady0 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7
         inst_10
         PState sched
         inst_13
         JobReady0 arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_7
         inst_10
         inst_13
         PState JobReady0 arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7
         arr_seq j ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_7
            inst_13 j) ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_7
            PState arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_7
            inst_13
            PState arr_seq sched JLFP)
         inst_10
         inst_13
         PState sched j t1 t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
               inst_7
               (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
                  inst_7
                  PState arr_seq sched JLFP)
               j t))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_7
            PState sched j t)
         Bool_true
```
