# `busy_interval_from_total_workload_bound`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.facts.busy_interval.carry_in.busy_interval_from_total_workload_bound`
- Lean: `Prosa.Analysis.Facts.BusyInterval.CarryIn.busy_interval_from_total_workload_bound`
- Certificate: `busy_interval_from_total_workload_bound_correspondence`

## Official Rocq

```coq
busy_interval_from_total_workload_bound :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
forall Δ : duration,
is_true (0 < Δ) ->
(forall t : instant,
 @no_carry_in Job H1 H2 arr_seq PState sched t ->
 is_true
   (@blackout_during Job PState sched t (t + Δ) + @total_workload_between Job H2 arr_seq t (t + Δ) <= Δ)) ->
@unit_service_proc_model Job PState ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
exists t1 t2 : nat,
  is_true (t1 <= @job_arrival Job H1 j < t2) /\
  is_true (t2 <= t1 + Δ) /\ @busy_interval Job H1 H2 PState arr_seq sched JLFP j t1 t2

busy_interval_from_total_workload_bound is not universe polymorphic
Arguments busy_interval_from_total_workload_bound {Job H1 H2} arr_seq H_valid_arr_seq 
  {PState} H_uniproc H_fully_consuming_proc_model sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute {JLFP} H_priority_is_reflexive 
  {JobReady0} H_job_ready H_work_conserving Δ H_delta_positive H_workload_is_bounded%function_scope
  H_unit_service_proc_model j H_from_arrival_sequence H_job_cost_positive
busy_interval_from_total_workload_bound is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.carry_in.busy_interval_from_total_workload_bound
Declared in library prosa.analysis.facts.busy_interval.carry_in, line 282, characters 10-49
@busy_interval_from_total_workload_bound
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall JobReady0 : @JobReady Job PState H2 H1,
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       forall Δ : duration,
       is_true (0 < Δ) ->
       (forall t : instant,
        @no_carry_in Job H1 H2 arr_seq PState sched t ->
        is_true
          (@blackout_during Job PState sched t (t + Δ) + @total_workload_between Job H2 arr_seq t (t + Δ) <=
           Δ)) ->
       @unit_service_proc_model Job PState ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       exists t1 t2 : nat,
         is_true (t1 <= @job_arrival Job H1 j < t2) /\
         is_true (t2 <= t1 + Δ) /\ @busy_interval Job H1 H2 PState arr_seq sched JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.CarryIn.busy_interval_from_total_workload_bound : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                  ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
                    Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                      ∀ [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
                        Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                          Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                            ∀ (Δ : Prosa.Behavior.Time.duration),
                              0 < Δ →
                                (∀ (t : Prosa.Behavior.Time.instant),
                                    Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched t →
                                      Prosa.Model.Processor.Supply.blackout_during sched t (t + Δ) +
                                          Prosa.Model.Aggregate.Workload.total_workload_between arr_seq t (t + Δ) ≤
                                        Δ) →
                                  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                                    ∀ (j : Job),
                                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                        Prosa.Model.Job.Properties.job_cost_positive j = true →
                                          ∃ t1 t2,
                                            (decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) &&
                                                  decide (Prosa.Behavior.Job.job_arrival j < t2)) =
                                                true ∧
                                              t2 ≤ t1 + Δ ∧
                                                Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval arr_seq
                                                  sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_CarryIn_busy_interval_from_total_workload_bound
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
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_9 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall
         inst_54 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_54 arr_seq sched JLFP ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_54 arr_seq sched ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) _UU0394_ ->
       (forall t : Prosa_Behavior_Time_instant,
        Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
          inst_3
          inst_6
          inst_9 arr_seq PState sched
          t ->
        LE_le_inst1 Nat instLENat
          (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
             (Prosa_Model_Processor_Supply_blackout_during Job
                inst_3 PState sched t
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                   _UU0394_))
             (Prosa_Model_Aggregate_Workload_total_workload_between Job
                inst_3
                inst_9 arr_seq t
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                   _UU0394_)))
          _UU0394_) ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       Exists Nat
         (fun t1 : Nat =>
          Exists Nat
            (fun t2 : Nat =>
             And
               (@eq Bool
                  (Bool_and
                     (Decidable_decide
                        (LE_le_inst1 Nat instLENat t1
                           (Prosa_Behavior_Job_JobArrival_job_arrival Job
                              inst_3
                              inst_6 j))
                        (Nat_decLe t1
                           (Prosa_Behavior_Job_JobArrival_job_arrival Job
                              inst_3
                              inst_6 j)))
                     (Decidable_decide
                        (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                           (Prosa_Behavior_Job_JobArrival_job_arrival Job
                              inst_3
                              inst_6 j)
                           t2)
                        (Nat_decLt
                           (Prosa_Behavior_Job_JobArrival_job_arrival Job
                              inst_3
                              inst_6 j)
                           t2)))
                  Bool_true)
               (And
                  (LE_le_inst1 Nat instLENat t2
                     (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) t1
                        _UU0394_))
                  (Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval Job
                     inst_3
                     inst_6
                     inst_9 PState
                     arr_seq sched JLFP j t1 t2))))
```
