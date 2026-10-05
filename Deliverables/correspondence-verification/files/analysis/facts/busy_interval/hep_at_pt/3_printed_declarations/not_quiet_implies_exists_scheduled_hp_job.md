# `not_quiet_implies_exists_scheduled_hp_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job`
- Lean: `Prosa.Analysis.Facts.BusyInterval.HepAtPt.not_quiet_implies_exists_scheduled_hp_job`
- Certificate: `not_quiet_implies_exists_scheduled_hp_job_correspondence`

## Official Rocq

```coq
not_quiet_implies_exists_scheduled_hp_job :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@transitive_job_priorities Job JLFP ->
forall {H4 : JobPreemptable Job},
@valid_preemption_model Job H2 H4 PState arr_seq sched ->
forall {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H1 H2 PState H4 JobReady0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
forall K : duration,
(exists pr_t : instant,
   is_true (@preemption_time Job H4 arr_seq PState sched pr_t) /\ is_true (t1 <= pr_t <= t1 + K)) ->
forall t : nat,
is_true (t1 + K <= t < t2) ->
exists j_hp : Equality.sort Job,
  is_true (@arrived_between Job H1 j_hp t1 t.+1) /\
  is_true (@hep_job Job JLFP j_hp j) /\ is_true (@scheduled_at Job PState sched j_hp t)

not_quiet_implies_exists_scheduled_hp_job is not universe polymorphic
Arguments not_quiet_implies_exists_scheduled_hp_job {Job H1 H2} arr_seq H_valid_arrivals 
  {PState} H_uni sched {JLFP} H_priority_is_reflexive H_priority_is_transitive {H4} 
  H_valid_preemption_model {JobReady0} H_job_ready H_sched_valid H_work_conserving 
  H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix 
  K H_preemption_time_exists t%nat_scope _
not_quiet_implies_exists_scheduled_hp_job is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job
Declared in library prosa.analysis.facts.busy_interval.hep_at_pt, line 354, characters 8-49
@not_quiet_implies_exists_scheduled_hp_job
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       @transitive_job_priorities Job JLFP ->
       forall H4 : JobPreemptable Job,
       @valid_preemption_model Job H2 H4 PState arr_seq sched ->
       forall JobReady0 : @JobReady Job PState H2 H1,
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H1 H2 PState H4 JobReady0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
       forall K : duration,
       (exists pr_t : instant,
          is_true (@preemption_time Job H4 arr_seq PState sched pr_t) /\ is_true (t1 <= pr_t <= t1 + K)) ->
       forall t : nat,
       is_true (t1 + K <= t < t2) ->
       exists j_hp : Equality.sort Job,
         is_true (@arrived_between Job H1 j_hp t1 t.+1) /\
         is_true (@hep_job Job JLFP j_hp j) /\ is_true (@scheduled_at Job PState sched j_hp t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.HepAtPt.not_quiet_implies_exists_scheduled_hp_job : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
          Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
            Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
              ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                  ∀ [inst_4 : Prosa.Behavior.Ready.JobReady Job PState],
                    Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                        Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                          Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                              JLFP →
                            ∀ (j : Job),
                              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                Prosa.Model.Job.Properties.job_cost_positive j = true →
                                  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                    Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched
                                        j t1 t2 →
                                      ∀ (K : Prosa.Behavior.Time.duration),
                                        (∃ pr_t,
                                            Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched pr_t =
                                                true ∧
                                              (decide (t1 ≤ pr_t) && decide (pr_t ≤ t1 + K)) = true) →
                                          ∀ (t : ℕ),
                                            (decide (t1 + K ≤ t) && decide (t < t2)) = true →
                                              ∃ j_hp,
                                                Prosa.Behavior.Arrival_sequence.arrived_between j_hp t1 (t + 1) = true ∧
                                                  Prosa.Model.Priority.Definitions.hep_job j_hp j = true ∧
                                                    Prosa.Behavior.Service.scheduled_at sched j_hp t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_HepAtPt_not_quiet_implies_exists_scheduled_hp_job
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
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         inst_38 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_38 PState arr_seq sched ->
       forall
         inst_47 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_47 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_47 arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_47 arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_38
         inst_47 arr_seq sched JLFP ->
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
         inst_9 PState arr_seq sched
         JLFP j t1 t2 ->
       forall K : Prosa_Behavior_Time_duration,
       Exists Prosa_Behavior_Time_instant
         (fun pr_t : Prosa_Behavior_Time_instant =>
          And
            (@eq Bool
               (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                  inst_3
                  inst_38 arr_seq
                  PState sched pr_t)
               Bool_true)
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 pr_t)
                     (Nat_decLe t1 pr_t))
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat pr_t
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                           Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 K))
                     (Nat_decLe pr_t
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                           Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 K))))
               Bool_true)) ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 K)
                  t)
               (Nat_decLe
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 K)
                  t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       Exists Job
         (fun j_hp : Job =>
          And
            (@eq Bool
               (Prosa_Behavior_Arrival_sequence_arrived_between Job
                  inst_3
                  inst_6 j_hp t1
                  (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
               Bool_true)
            (And
               (@eq Bool
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_3 JLFP j_hp
                     j)
                  Bool_true)
               (@eq Bool
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState
                     sched j_hp t)
                  Bool_true)))
```
