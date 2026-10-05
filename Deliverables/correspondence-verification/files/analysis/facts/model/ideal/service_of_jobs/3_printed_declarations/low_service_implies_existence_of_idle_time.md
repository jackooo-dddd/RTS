# `low_service_implies_existence_of_idle_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs.low_service_implies_existence_of_idle_time`
- Certificate: `low_service_implies_existence_of_idle_time_correspondence`

## Official Rocq

```coq
low_service_implies_existence_of_idle_time :
forall {Job : JobType} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@ideal_progress_proc_model Job PState ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H0 PState sched ->
forall t1 t2 : instant,
is_true
  (@service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
     (@arrivals_between Job arr_seq 0 t2) t1 t2 <
   t2 - t1) ->
exists t : nat, is_true (t1 <= t < t2) /\ is_true (@is_idle Job PState arr_seq sched t)

low_service_implies_existence_of_idle_time is not universe polymorphic
Arguments low_service_implies_existence_of_idle_time {Job H0} arr_seq H_valid_arrival_sequence 
  {PState} H_uniproc H_ideal_progress_proc_model sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute t1 t2 _
low_service_implies_existence_of_idle_time is opaque
Expands to: Constant
            prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time
Declared in library prosa.analysis.facts.model.ideal.service_of_jobs, line 119, characters 8-50
@low_service_implies_existence_of_idle_time
     : forall (Job : JobType) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       @ideal_progress_proc_model Job PState ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       forall t1 t2 : instant,
       is_true
         (@service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
            (@arrivals_between Job arr_seq 0 t2) t1 t2 <
          t2 - t1) ->
       exists t : nat, is_true (t1 <= t < t2) /\ is_true (@is_idle Job PState arr_seq sched t)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs.low_service_implies_existence_of_idle_time : ∀
  (Job : Prosa.Behavior.Job.JobType) [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun x => true)
                        (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 t2) t1 t2 <
                      t2 - t1 →
                    ∃ t,
                      (decide (t1 ≤ t) && decide (t < t2)) = true ∧
                        Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_ServiceOfJobs_low_service_implies_existence_of_idle_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
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
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched
         arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       LT_lt_inst1 Nat instLTNat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched
            (fun _ : Job => Bool_true)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t2)
            t1 t2)
         (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1) ->
       Exists Nat
         (fun t : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
               Bool_true)
            (@eq Bool
               (Prosa_Model_Schedule_Scheduled_is_idle Job
                  inst_3 PState
                  arr_seq sched t)
               Bool_true))
```
