# `preemption_time_le_max_len_of_np_segment`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi.preemption_time_le_max_len_of_np_segment`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.preemption_time_le_max_len_of_np_segment`
- Certificate: `preemption_time_le_max_len_of_np_segment_correspondence`

## Official Rocq

```coq
preemption_time_le_max_len_of_np_segment :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@transitive_job_priorities Job JLFP ->
forall {H4 : JobPreemptable Job},
@valid_preemption_model Job H2 H4 PState arr_seq sched ->
forall {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
@respects_JLFP_policy_at_preemption_point Job H1 H2 PState H4 JobReady0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
forall jlp : Equality.sort Job,
is_true (@scheduled_at Job PState sched jlp t1) ->
is_true (~~ @hep_job Job JLFP jlp j) ->
forall fpt : instant,
is_true (@job_preemptable Job H4 jlp (@service Job PState sched jlp t1 + fpt)) ->
is_true (fpt <= @job_max_nonpreemptive_segment Job H2 H4 jlp - 1) ->
is_true (t1 <= t1 + fpt <= t1 + @max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1)

preemption_time_le_max_len_of_np_segment is not universe polymorphic
Arguments preemption_time_le_max_len_of_np_segment {Job H1 H2} arr_seq H_valid_arrivals 
  {PState} H_uni sched {JLFP} H_priority_is_transitive {H4} H_valid_preemption_model 
  {JobReady0} H_job_ready H_sched_valid H_respects_policy j H_j_arrives H_job_cost_positive 
  t1 t2 H_busy_interval_prefix jlp H_jlp_is_scheduled H_jlp_low_priority fpt H_fpt_is_preemption_point
  H_progr_le_max_nonp_segment
preemption_time_le_max_len_of_np_segment is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi.preemption_time_le_max_len_of_np_segment
Declared in library prosa.analysis.facts.busy_interval.pi, line 560, characters 16-56
@preemption_time_le_max_len_of_np_segment
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (JLFP : JLFP_policy Job),
       @transitive_job_priorities Job JLFP ->
       forall H4 : JobPreemptable Job,
       @valid_preemption_model Job H2 H4 PState arr_seq sched ->
       forall JobReady0 : @JobReady Job PState H2 H1,
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job H1 H2 PState H4 JobReady0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
       forall jlp : Equality.sort Job,
       is_true (@scheduled_at Job PState sched jlp t1) ->
       is_true (~~ @hep_job Job JLFP jlp j) ->
       forall fpt : instant,
       is_true (@job_preemptable Job H4 jlp (@service Job PState sched jlp t1 + fpt)) ->
       is_true (fpt <= @job_max_nonpreemptive_segment Job H2 H4 jlp - 1) ->
       is_true (t1 <= t1 + fpt <= t1 + @max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.preemption_time_le_max_len_of_np_segment : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
          Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
            ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                ∀ [inst_4 : Prosa.Behavior.Ready.JobReady Job PState],
                  Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                    Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                      Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                        ∀ (j : Job),
                          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                            Prosa.Model.Job.Properties.job_cost_positive j = true →
                              ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j
                                    t1 t2 →
                                  ∀ (jlp : Job),
                                    Prosa.Behavior.Service.scheduled_at sched jlp t1 = true →
                                      (!Prosa.Model.Priority.Definitions.hep_job jlp j) = true →
                                        ∀ (fpt : Prosa.Behavior.Time.instant),
                                          Prosa.Model.Preemption.Parameter.job_preemptable jlp
                                                (Prosa.Behavior.Service.service sched jlp t1 + fpt) =
                                              true →
                                            fpt ≤
                                                Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment jlp - 1 →
                                              (decide (t1 ≤ t1 + fpt) &&
                                                  decide
                                                    (t1 + fpt ≤
                                                      t1 +
                                                        Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment
                                                          arr_seq j t1)) =
                                                true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_le_max_len_of_np_segment
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         inst_35 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_35 PState arr_seq sched ->
       forall
         inst_44 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_44 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_44 arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_35
         inst_44 arr_seq sched JLFP ->
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
         inst_9 PState arr_seq sched JLFP
         j t1 t2 ->
       forall jlp : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jlp t1)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3 JLFP jlp j))
         Bool_true ->
       forall fpt : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
            inst_3
            inst_35 jlp
            (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_instant Prosa_Behavior_Job_work
               (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
               (Prosa_Behavior_Service_service Job
                  inst_3 PState sched jlp
                  t1)
               fpt))
         Bool_true ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat fpt
         (HSub_hSub_inst7 Nat Prosa_Behavior_Time_instant Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
               inst_3
               inst_9
               inst_35 jlp)
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     fpt))
               (Nat_decLe t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     fpt)))
            (Decidable_decide
               (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     fpt)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
                        inst_3
                        inst_9 arr_seq
                        JLFP inst_35 j t1)))
               (Nat_decLe
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     fpt)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
                        inst_3
                        inst_9 arr_seq
                        JLFP inst_35 j t1)))))
         Bool_true
```
