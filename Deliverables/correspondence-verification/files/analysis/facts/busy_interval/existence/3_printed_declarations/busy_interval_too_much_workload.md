# `busy_interval_too_much_workload`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.busy_interval_too_much_workload`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_too_much_workload`
- Certificate: `busy_interval_too_much_workload_correspondence`

## Official Rocq

```coq
busy_interval_too_much_workload :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job Arrival PState sched ->
@completed_jobs_dont_execute Job PState sched Cost ->
forall {JLFP : JLFP_policy Job} (j : Equality.sort Job),
@arrival_sequence_uniq Job arr_seq ->
forall t_busy : instant,
@unit_service_proc_model Job PState ->
forall t1 : instant,
(fun t2 : instant => [eta @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t2]) t1
  t_busy.+1 ->
forall delta : duration,
is_true (0 < delta) ->
(forall t : nat,
 is_true (t1 < t <= t1 + delta) -> ~ [eta @quiet_time Job Arrival Cost PState arr_seq sched JLFP j] t) ->
is_true
  ((fun t2 t3 : instant =>
    @service_of_higher_or_equal_priority_jobs Job PState sched JLFP (@arrivals_between Job arr_seq t2 t3) j
      t2 t3)
     t1 (t1 + delta) <
   (fun t2 : instant => [eta @workload_of_hep_jobs Job Cost arr_seq JLFP j t2]) t1 (t1 + delta))

busy_interval_too_much_workload is not universe polymorphic
Arguments busy_interval_too_much_workload {Job Arrival Cost} arr_seq H_valid_arrival_time 
  {PState} sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute {JLFP} 
  j H_arrival_sequence_is_a_set t_busy H_unit t1 H_is_busy_prefix delta H_delta_positive
  H_no_quiet_time%function_scope
busy_interval_too_much_workload is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.busy_interval_too_much_workload
Declared in library prosa.analysis.facts.busy_interval.existence, line 509, characters 16-47
@busy_interval_too_much_workload
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job Arrival PState sched ->
       @completed_jobs_dont_execute Job PState sched Cost ->
       forall (JLFP : JLFP_policy Job) (j : Equality.sort Job),
       @arrival_sequence_uniq Job arr_seq ->
       forall t_busy : instant,
       @unit_service_proc_model Job PState ->
       forall t1 : instant,
       @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t_busy.+1 ->
       forall delta : duration,
       is_true (0 < delta) ->
       (forall t : nat,
        is_true (t1 < t <= t1 + delta) -> ~ @quiet_time Job Arrival Cost PState arr_seq sched JLFP j t) ->
       is_true
         (@service_of_higher_or_equal_priority_jobs Job PState sched JLFP
            (@arrivals_between Job arr_seq t1 (t1 + delta)) j t1 (t1 + delta) <
          @workload_of_hep_jobs Job Cost arr_seq JLFP j t1 (t1 + delta))
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_too_much_workload : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
        Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
          ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job),
            Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
              ∀ (t_busy : Prosa.Behavior.Time.instant),
                Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                  ∀ (t1 : Prosa.Behavior.Time.instant),
                    Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1
                        (t_busy + 1) →
                      ∀ (delta : Prosa.Behavior.Time.duration),
                        0 < delta →
                          (∀ (t : ℕ),
                              (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
                                ¬Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t) →
                            Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs sched
                                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + delta)) j t1
                                (t1 + delta) <
                              Prosa.Model.Aggregate.Workload.workload_of_hep_jobs arr_seq j t1 (t1 + delta)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_busy_interval_too_much_workload
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
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_9 ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq ->
       forall t_busy : Prosa_Behavior_Time_instant,
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall t1 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched JLFP j t1
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t_busy
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       forall delta : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) delta ->
       (forall t : Nat,
        @eq Bool
          (Bool_and
             (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
             (Decidable_decide
                (LE_le_inst1 Nat instLENat t
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                      delta))
                (Nat_decLe t
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                      delta))))
          Bool_true ->
        Not
          (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
             inst_3
             inst_6
             inst_9 PState arr_seq
             sched JLFP j t)) ->
       LT_lt_inst1 Nat instLTNat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs Job
            inst_3 PState sched
            JLFP
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  delta))
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 delta))
         (Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job
            inst_3
            inst_9 arr_seq JLFP j
            t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 delta))
```
