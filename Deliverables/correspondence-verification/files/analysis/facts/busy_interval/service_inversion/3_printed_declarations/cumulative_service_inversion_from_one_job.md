# `cumulative_service_inversion_from_one_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.cumulative_service_inversion_from_one_job`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.cumulative_service_inversion_from_one_job`
- Certificate: `cumulative_service_inversion_from_one_job_correspondence`

## Official Rocq

```coq
cumulative_service_inversion_from_one_job :
forall {Job : JobType} {H2 : JobArrival Job} {H3 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@transitive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H2 arr_seq ->
forall (sched : @schedule Job PState) {JobReady0 : @JobReady Job PState H3 H2},
@work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
forall {H4 : JobPreemptable Job},
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H3 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H2 H3 PState arr_seq sched JLFP j t1 t2 ->
forall t : instant,
is_true (t <= t2) ->
is_true (0 < @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t) ->
exists jlp : Equality.sort Job,
  is_true (@job_arrival Job H2 jlp < t1) /\
  is_true (~~ @hep_job Job JLFP jlp j) /\
  @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t =
  @service_during Job PState sched jlp t1 t

cumulative_service_inversion_from_one_job is not universe polymorphic
Arguments cumulative_service_inversion_from_one_job {Job H2 H3 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model {JLFP} H_priority_is_reflexive H_priority_is_transitive 
  arr_seq H_valid_arrival_sequence sched {JobReady0} H_job_ready H_sched_valid {H4} 
  H_valid_preemption_model H_respects_policy j H_j_arrives H_job_cost_positive t1 
  t2 H_busy_prefix t H_t_le_t2 H_service_inversion_positive
cumulative_service_inversion_from_one_job is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.service_inversion.cumulative_service_inversion_from_one_job
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 295, characters 10-51
@cumulative_service_inversion_from_one_job
     : forall (Job : JobType) (H2 : JobArrival Job) (H3 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       @transitive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H2 arr_seq ->
       forall (sched : @schedule Job PState) (JobReady0 : @JobReady Job PState H3 H2),
       @work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
       forall H4 : JobPreemptable Job,
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H3 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H2 H3 PState arr_seq sched JLFP j t1 t2 ->
       forall t : instant,
       is_true (t <= t2) ->
       is_true (0 < @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t) ->
       exists jlp : Equality.sort Job,
         is_true (@job_arrival Job H2 jlp < t1) /\
         is_true (~~ @hep_job Job JLFP jlp j) /\
         @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t =
         @service_during Job PState sched jlp t1 t
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.cumulative_service_inversion_from_one_job : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
        Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
          Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
                ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
                  Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                    Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                      ∀ [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                        Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                          Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                              JLFP →
                            ∀ (j : Job),
                              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                Prosa.Model.Job.Properties.job_cost_positive j = true →
                                  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                    Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched
                                        j t1 t2 →
                                      ∀ t ≤ t2,
                                        0 <
                                            Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion
                                              arr_seq sched j t1 t →
                                          ∃ jlp,
                                            Prosa.Behavior.Job.job_arrival jlp < t1 ∧
                                              (!Prosa.Model.Priority.Definitions.hep_job jlp j) = true ∧
                                                Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion
                                                    arr_seq sched j t1 t =
                                                  Prosa.Behavior.Service.service_during sched jlp t1 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_cumulative_service_inversion_from_one_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState)
         (inst_45 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_45 arr_seq
         sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_45 arr_seq ->
       forall
         inst_59 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_59 PState
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_59
         inst_45 arr_seq
         sched JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState
         arr_seq sched JLFP j t1 t2 ->
       forall t : Prosa_Behavior_Time_instant,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t2 ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
            inst_3 PState
            arr_seq sched
            (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
               inst_3 JLFP)
            j t1 t) ->
       Exists Job
         (fun jlp : Job =>
          And
            (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_6 jlp)
               t1)
            (And
               (@eq Bool
                  (Bool_not
                     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                        inst_3
                        JLFP jlp j))
                  Bool_true)
               (@eq Nat
                  (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
                     inst_3
                     PState arr_seq sched
                     (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
                        inst_3
                        JLFP)
                     j t1 t)
                  (Prosa_Behavior_Service_service_during Job
                     inst_3
                     PState sched jlp t1 t))))
```
