# `low_total_service_implies_existence_of_time_with_no_carry_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.carry_in.low_total_service_implies_existence_of_time_with_no_carry_in`
- Lean: `Prosa.Analysis.Facts.BusyInterval.CarryIn.low_total_service_implies_existence_of_time_with_no_carry_in`
- Certificate: `low_total_service_implies_existence_of_time_with_no_carry_in_correspondence`

## Official Rocq

```coq
low_total_service_implies_existence_of_time_with_no_carry_in :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job} {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
forall Δ : duration,
is_true (0 < Δ) ->
forall t : duration,
is_true
  (@blackout_during Job PState sched t (t + Δ) +
   (fun t1 t2 : instant =>
    @service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
      (@arrivals_between Job arr_seq 0 t2) t1 t2)
     t (t + Δ) <
   Δ) ->
exists δ : nat, is_true (δ < Δ) /\ @no_carry_in Job H1 H2 arr_seq PState sched (t.+1 + δ)

low_total_service_implies_existence_of_time_with_no_carry_in is not universe polymorphic
Arguments low_total_service_implies_existence_of_time_with_no_carry_in {Job H1 H2} 
  arr_seq H_valid_arr_seq {PState} H_uniproc H_fully_consuming_proc_model sched
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP JobReady0} 
  H_job_ready H_work_conserving Δ H_delta_positive t _
low_total_service_implies_existence_of_time_with_no_carry_in is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.carry_in.low_total_service_implies_existence_of_time_with_no_carry_in
Declared in library prosa.analysis.facts.busy_interval.carry_in, line 183, characters 10-70
@low_total_service_implies_existence_of_time_with_no_carry_in
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (JLFP : JLFP_policy Job) (JobReady0 : @JobReady Job PState H2 H1),
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       forall Δ : duration,
       is_true (0 < Δ) ->
       forall t : duration,
       is_true
         (@blackout_during Job PState sched t (t + Δ) +
          @service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
            (@arrivals_between Job arr_seq 0 (t + Δ)) t (t + Δ) <
          Δ) ->
       exists δ : nat, is_true (δ < Δ) /\ @no_carry_in Job H1 H2 arr_seq PState sched (t.+1 + δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.CarryIn.low_total_service_implies_existence_of_time_with_no_carry_in : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
                  [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
                  Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                      ∀ (Δ : Prosa.Behavior.Time.duration),
                        0 < Δ →
                          ∀ (t : Prosa.Behavior.Time.duration),
                            Prosa.Model.Processor.Supply.blackout_during sched t (t + Δ) +
                                  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun x => true)
                                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) <
                                Δ →
                              ∃ δ < Δ, Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched (t + 1 + δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_CarryIn_low_total_service_implies_existence_of_time_with_no_carry_in
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
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_44 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_44 arr_seq sched JLFP ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_44 arr_seq sched ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) _UU0394_ ->
       forall t : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Nat instLTNat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Processor_Supply_blackout_during Job
               inst_3 PState sched t
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t
                  _UU0394_))
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched
               (fun _ : Job => Bool_true)
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t
                     _UU0394_))
               t
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t
                  _UU0394_)))
         _UU0394_ ->
       Exists Nat
         (fun _UU03b4_ : Nat =>
          And (LT_lt_inst1 Nat instLTNat _UU03b4_ _UU0394_)
            (Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
               inst_3
               inst_6
               inst_9 arr_seq PState
               sched
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                  (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
                  _UU03b4_)))
```
