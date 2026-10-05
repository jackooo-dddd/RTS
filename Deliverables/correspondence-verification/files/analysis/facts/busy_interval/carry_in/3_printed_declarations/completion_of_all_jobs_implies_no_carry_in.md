# `completion_of_all_jobs_implies_no_carry_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.carry_in.completion_of_all_jobs_implies_no_carry_in`
- Lean: `Prosa.Analysis.Facts.BusyInterval.CarryIn.completion_of_all_jobs_implies_no_carry_in`
- Certificate: `completion_of_all_jobs_implies_no_carry_in_correspondence`

## Official Rocq

```coq
completion_of_all_jobs_implies_no_carry_in :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
forall Δ : duration,
(forall t : instant,
 @no_carry_in Job H1 H2 arr_seq PState sched t ->
 is_true
   (@blackout_during Job PState sched t (t + Δ) + @total_workload_between Job H2 arr_seq t (t + Δ) <= Δ)) ->
@unit_service_proc_model Job PState ->
forall t : duration,
@no_carry_in Job H1 H2 arr_seq PState sched t ->
@blackout_during Job PState sched t (t + Δ) +
(fun t1 t2 : instant =>
 @service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
   (@arrivals_between Job arr_seq 0 t2) t1 t2)
  t (t + Δ) =
Δ -> @no_carry_in Job H1 H2 arr_seq PState sched (t + Δ)

completion_of_all_jobs_implies_no_carry_in is not universe polymorphic
Arguments completion_of_all_jobs_implies_no_carry_in {Job H1 H2} arr_seq H_valid_arr_seq 
  {PState} sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute Δ
  H_workload_is_bounded%function_scope H_unit_service_proc_model t H_no_carry_in 
  _ j_o _ _
completion_of_all_jobs_implies_no_carry_in is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.carry_in.completion_of_all_jobs_implies_no_carry_in
Declared in library prosa.analysis.facts.busy_interval.carry_in, line 218, characters 10-52
@completion_of_all_jobs_implies_no_carry_in
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       forall Δ : duration,
       (forall t : instant,
        @no_carry_in Job H1 H2 arr_seq PState sched t ->
        is_true
          (@blackout_during Job PState sched t (t + Δ) + @total_workload_between Job H2 arr_seq t (t + Δ) <=
           Δ)) ->
       @unit_service_proc_model Job PState ->
       forall t : duration,
       @no_carry_in Job H1 H2 arr_seq PState sched t ->
       @blackout_during Job PState sched t (t + Δ) +
       @service_of_jobs Job PState sched (pred_of_simpl (@predT (Equality.sort Job)))
         (@arrivals_between Job arr_seq 0 (t + Δ)) t (t + Δ) =
       Δ -> @no_carry_in Job H1 H2 arr_seq PState sched (t + Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.CarryIn.completion_of_all_jobs_implies_no_carry_in : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
        Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
          ∀ (Δ : Prosa.Behavior.Time.duration),
            (∀ (t : Prosa.Behavior.Time.instant),
                Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched t →
                  Prosa.Model.Processor.Supply.blackout_during sched t (t + Δ) +
                      Prosa.Model.Aggregate.Workload.total_workload_between arr_seq t (t + Δ) ≤
                    Δ) →
              Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                ∀ (t : Prosa.Behavior.Time.duration),
                  Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched t →
                    Prosa.Model.Processor.Supply.blackout_during sched t (t + Δ) +
                          Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun x => true)
                            (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) =
                        Δ →
                      Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched (t + Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_CarryIn_completion_of_all_jobs_implies_no_carry_in
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
       forall _UU0394_ : Prosa_Behavior_Time_duration,
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
       forall t : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
         inst_3
         inst_6
         inst_9 arr_seq PState sched
         t ->
       @eq Nat
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
       Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
         inst_3
         inst_6
         inst_9 arr_seq PState sched
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t _UU0394_)
```
