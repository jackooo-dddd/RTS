# `hep_jobs_receive_no_service_before_quiet_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.hep_jobs_receive_no_service_before_quiet_time`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.hep_jobs_receive_no_service_before_quiet_time`
- Certificate: `hep_jobs_receive_no_service_before_quiet_time_correspondence`

## Official Rocq

```coq
hep_jobs_receive_no_service_before_quiet_time :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@completed_jobs_dont_execute Job PState sched Cost ->
forall {JLFP : JLFP_policy Job} (j : Equality.sort Job) (t1 : instant),
forall Δ : duration,
(fun t_beg t_end : instant =>
 @service_of_higher_or_equal_priority_jobs Job PState sched JLFP (@arrivals_between Job arr_seq t_beg t_end)
   j t1 (t1 + Δ))
  t1 (t1 + Δ) =
(fun t_beg t_end : instant =>
 @service_of_higher_or_equal_priority_jobs Job PState sched JLFP (@arrivals_between Job arr_seq t_beg t_end)
   j t1 (t1 + Δ))
  0 (t1 + Δ)

hep_jobs_receive_no_service_before_quiet_time is not universe polymorphic
Arguments hep_jobs_receive_no_service_before_quiet_time {Job Arrival Cost} arr_seq 
  H_valid_arrival_time {PState} sched H_completed_jobs_dont_execute {JLFP} j t1 H_quiet_time 
  Δ
hep_jobs_receive_no_service_before_quiet_time is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.existence.hep_jobs_receive_no_service_before_quiet_time
Declared in library prosa.analysis.facts.busy_interval.existence, line 260, characters 10-55
@hep_jobs_receive_no_service_before_quiet_time
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @completed_jobs_dont_execute Job PState sched Cost ->
       forall (JLFP : JLFP_policy Job) (j : Equality.sort Job) (t1 : instant),
       @quiet_time Job Arrival Cost PState arr_seq sched JLFP j t1 ->
       forall Δ : duration,
       @service_of_higher_or_equal_priority_jobs Job PState sched JLFP
         (@arrivals_between Job arr_seq t1 (t1 + Δ)) j t1 (t1 + Δ) =
       @service_of_higher_or_equal_priority_jobs Job PState sched JLFP
         (@arrivals_between Job arr_seq 0 (t1 + Δ)) j t1 (t1 + Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.hep_jobs_receive_no_service_before_quiet_time : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
        ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job) (t1 : Prosa.Behavior.Time.instant),
          Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t1 →
            ∀ (Δ : Prosa.Behavior.Time.duration),
              Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs sched
                  (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) j t1 (t1 + Δ) =
                Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs sched
                  (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 (t1 + Δ)) j t1 (t1 + Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_hep_jobs_receive_no_service_before_quiet_time
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
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_9 ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job) (t1 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched JLFP j t1 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs Job
            inst_3 PState sched
            JLFP
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_))
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs Job
            inst_3 PState sched
            JLFP
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_))
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
```
