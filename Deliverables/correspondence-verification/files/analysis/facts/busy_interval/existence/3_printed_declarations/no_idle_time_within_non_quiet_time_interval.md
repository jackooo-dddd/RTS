# `no_idle_time_within_non_quiet_time_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.no_idle_time_within_non_quiet_time_interval`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.no_idle_time_within_non_quiet_time_interval`
- Certificate: `no_idle_time_within_non_quiet_time_interval_correspondence`

## Official Rocq

```coq
no_idle_time_within_non_quiet_time_interval :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job Arrival PState sched ->
forall {JLFP : JLFP_policy Job} {H0 : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@work_conserving Job Arrival Cost PState H0 arr_seq sched ->
@arrival_sequence_uniq Job arr_seq ->
forall (t1 : instant) (Δ : duration),
(forall t : nat,
 is_true (t1 < t <= t1 + Δ) -> ~ [eta @quiet_time Job Arrival Cost PState arr_seq sched JLFP j] t) ->
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
@ideal_progress_proc_model Job PState ->
@total_service_of_jobs_in Job PState sched (@arrivals_between Job arr_seq 0 (t1 + Δ)) t1 (t1 + Δ) = Δ

no_idle_time_within_non_quiet_time_interval is not universe polymorphic
Arguments no_idle_time_within_non_quiet_time_interval {Job Arrival Cost} arr_seq 
  H_valid_arrival_time {PState} sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  {JLFP H0} H_job_ready j H_work_conserving H_arrival_sequence_is_a_set t1 Δ H_no_quiet_time%function_scope
  H_uni H_unit H_progress
no_idle_time_within_non_quiet_time_interval is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.no_idle_time_within_non_quiet_time_interval
Declared in library prosa.analysis.facts.busy_interval.existence, line 292, characters 10-53
@no_idle_time_within_non_quiet_time_interval
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job Arrival PState sched ->
       forall (JLFP : JLFP_policy Job) (H0 : @JobReady Job PState Cost Arrival),
       @work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @work_conserving Job Arrival Cost PState H0 arr_seq sched ->
       @arrival_sequence_uniq Job arr_seq ->
       forall (t1 : instant) (Δ : duration),
       (forall t : nat,
        is_true (t1 < t <= t1 + Δ) -> ~ @quiet_time Job Arrival Cost PState arr_seq sched JLFP j t) ->
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       @ideal_progress_proc_model Job PState ->
       @total_service_of_jobs_in Job PState sched (@arrivals_between Job arr_seq 0 (t1 + Δ)) t1 (t1 + Δ) = Δ
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.no_idle_time_within_non_quiet_time_interval : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
            [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
            Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
              ∀ (j : Job),
                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
                    ∀ (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration),
                      (∀ (t : ℕ),
                          (decide (t1 < t) && decide (t ≤ t1 + Δ)) = true →
                            ¬Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t) →
                        Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
                          Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                            Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
                              Prosa.Model.Aggregate.ServiceOfJobs.total_service_of_jobs_in sched
                                  (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 (t1 + Δ)) t1 (t1 + Δ) =
                                Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_no_idle_time_within_non_quiet_time_interval
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
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched
         arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_34 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched JLFP ->
       forall j : Job,
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq ->
       forall (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration),
       (forall t : Nat,
        @eq Bool
          (Bool_and
             (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
             (Decidable_decide
                (LE_le_inst1 Nat instLENat t
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                      _UU0394_))
                (Nat_decLe t
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                      _UU0394_))))
          Bool_true ->
        Not
          (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
             inst_3
             inst_6
             inst_9 PState arr_seq
             sched JLFP j t)) ->
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in Job
            inst_3 PState sched
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_))
            t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         _UU0394_
```
