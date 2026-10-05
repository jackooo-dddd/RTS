# `pending_hep_job_exists_inside_busy_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_readiness.pending_hep_job_exists_inside_busy_interval`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.pending_hep_job_exists_inside_busy_interval`
- Certificate: `pending_hep_job_exists_inside_busy_interval_correspondence`

## Official Rocq

```coq
pending_hep_job_exists_inside_busy_interval :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
forall {JobReady0 : @JobReady Job PState H2 H1} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_cost Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H1 H2 PState sched
  (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
  (@rs_readiness_jlfp_interfering_workload Job H1 H2 PState JobReady0 arr_seq sched JLFP) j t1 t2 ->
forall t : instant,
is_true (t1 <= t < t2) ->
exists jhp : Equality.sort Job,
  @arrives_in Job arr_seq jhp /\
  is_true (@pending Job PState sched H2 H1 jhp t) /\ is_true (@hep_job Job JLFP jhp j)

pending_hep_job_exists_inside_busy_interval is not universe polymorphic
Arguments pending_hep_job_exists_inside_busy_interval {Job H1 H2 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model {JobReady0} arr_seq H_valid_arrival_sequence sched H_valid_schedule 
  {JLFP} H_priority_is_reflexive j H_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix 
  t H_t_in_busy_interval
pending_hep_job_exists_inside_busy_interval is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_readiness.pending_hep_job_exists_inside_busy_interval
Declared in library prosa.analysis.abstract.restricted_supply.iw_readiness, line 462, characters 12-55
@pending_hep_job_exists_inside_busy_interval
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       forall (JobReady0 : @JobReady Job PState H2 H1) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (0 < @job_cost Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H1 H2 PState sched
         (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
         (@rs_readiness_jlfp_interfering_workload Job H1 H2 PState JobReady0 arr_seq sched JLFP) j t1 t2 ->
       forall t : instant,
       is_true (t1 <= t < t2) ->
       exists jhp : Equality.sort Job,
         @arrives_in Job arr_seq jhp /\
         is_true (@pending Job PState sched H2 H1 jhp t) /\ is_true (@hep_job Job JLFP jhp j)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.pending_hep_job_exists_inside_busy_interval : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job PState]
        (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
                Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                  ∀ (j : Job),
                    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                      0 < Prosa.Behavior.Job.job_cost j →
                        ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                          Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
                            ∀ (t : Prosa.Behavior.Time.instant),
                              (decide (t1 ≤ t) && decide (t < t2)) = true →
                                ∃ jhp,
                                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jhp ∧
                                    Prosa.Behavior.Service.pending sched jhp t = true ∧
                                      Prosa.Model.Priority.Definitions.hep_job jhp j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_pending_hep_job_exists_inside_busy_interval
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
       forall
         (JobReady0 : Prosa_Behavior_Ready_JobReady Job
                        inst_7
                        PState
                        inst_13
                        inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7
         inst_10 PState
         sched inst_13
         JobReady0 arr_seq ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_7
            inst_13 j) ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
            inst_7
            inst_10
            inst_13 PState
            JobReady0 arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload Job
            inst_7
            inst_10
            inst_13 PState
            JobReady0 arr_seq sched JLFP)
         inst_10
         inst_13 PState
         sched j t1 t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       Exists Job
         (fun jhp : Job =>
          And
            (Prosa_Behavior_Arrival_sequence_arrives_in Job
               inst_7
               arr_seq jhp)
            (And
               (@eq Bool
                  (Prosa_Behavior_Service_pending Job
                     inst_7
                     PState sched
                     inst_13
                     inst_10
                     jhp t)
                  Bool_true)
               (@eq Bool
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_7
                     JLFP jhp j)
                  Bool_true)))
```
