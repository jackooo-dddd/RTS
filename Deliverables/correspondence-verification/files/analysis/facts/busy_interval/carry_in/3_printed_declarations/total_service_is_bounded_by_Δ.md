# `total_service_is_bounded_by_Δ`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.carry_in.total_service_is_bounded_by_Δ`
- Lean: `Prosa.Analysis.Facts.BusyInterval.CarryIn.total_service_is_bounded_by_Δ`
- Certificate: `total_service_is_bounded_by_Δ_correspondence`

## Official Rocq

```coq
total_service_is_bounded_by_Δ :
forall {Job : JobType} {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) (Δ : duration),
@unit_service_proc_model Job PState ->
forall t : duration,
is_true
  (@blackout_during Job PState sched t (t + Δ) +
   (fun t1 t2 : instant =>
    @service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
      (@arrivals_between Job arr_seq 0 t2) t1 t2)
     t (t + Δ) <=
   Δ)

total_service_is_bounded_by_Δ is not universe polymorphic
Arguments total_service_is_bounded_by_Δ {Job H1} arr_seq H_valid_arr_seq {PState} 
  H_uniproc sched Δ H_unit_service_proc_model t
total_service_is_bounded_by_Δ is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.carry_in.total_service_is_bounded_by_Δ
Declared in library prosa.analysis.facts.busy_interval.carry_in, line 158, characters 10-40
@total_service_is_bounded_by_Δ
     : forall (Job : JobType) (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (Δ : duration),
       @unit_service_proc_model Job PState ->
       forall t : duration,
       is_true
         (@blackout_during Job PState sched t (t + Δ) +
          @service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
            (@arrivals_between Job arr_seq 0 (t + Δ)) t (t + Δ) <=
          Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.CarryIn.total_service_is_bounded_by_Δ : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (Δ : Prosa.Behavior.Time.duration),
          Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
            ∀ (t : Prosa.Behavior.Time.duration),
              Prosa.Model.Processor.Supply.blackout_during sched t (t + Δ) +
                  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun x => true)
                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) ≤
                Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_CarryIn_total_service_is_bounded_by__UU0394_
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
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
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (_UU0394_ : Prosa_Behavior_Time_duration),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall t : Prosa_Behavior_Time_duration,
       LE_le_inst1 Nat instLENat
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
         _UU0394_
```
