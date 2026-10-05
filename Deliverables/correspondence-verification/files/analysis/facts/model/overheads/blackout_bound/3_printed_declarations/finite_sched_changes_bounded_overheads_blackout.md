# `finite_sched_changes_bounded_overheads_blackout`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.blackout_bound.finite_sched_changes_bounded_overheads_blackout`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.finite_sched_changes_bounded_overheads_blackout`
- Certificate: `finite_sched_changes_bounded_overheads_blackout_correspondence`

## Official Rocq

```coq
finite_sched_changes_bounded_overheads_blackout :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (DB CSB CRPDB : duration),
@overhead_resource_model Job sched DB CSB CRPDB ->
forall (k : nat) (t1 t2 : instant),
@number_schedule_changes Job sched t1.+1 t2 = k ->
is_true (@blackout_during Job (processor_state Job) sched t1 t2 <= (DB + CSB + CRPDB) * (k + 1))

finite_sched_changes_bounded_overheads_blackout is not universe polymorphic
Arguments finite_sched_changes_bounded_overheads_blackout {Job} sched DB CSB CRPDB 
  H_valid_overheads_model k%nat_scope t1 t2 _
finite_sched_changes_bounded_overheads_blackout is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.blackout_bound.finite_sched_changes_bounded_overheads_blackout
Declared in library prosa.analysis.facts.model.overheads.blackout_bound, line 275, characters 8-55
@finite_sched_changes_bounded_overheads_blackout
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (DB CSB CRPDB : duration),
       @overhead_resource_model Job sched DB CSB CRPDB ->
       forall (k : nat) (t1 t2 : instant),
       @number_schedule_changes Job sched t1.+1 t2 = k ->
       is_true (@blackout_during Job (processor_state Job) sched t1 t2 <= (DB + CSB + CRPDB) * (k + 1))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.finite_sched_changes_bounded_overheads_blackout : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (DB CSB CRPDB : Prosa.Behavior.Time.duration),
  Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model sched DB CSB CRPDB →
    ∀ (k : ℕ) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched (t1 + 1) t2 = k →
        Prosa.Model.Processor.Supply.blackout_during sched t1 t2 ≤ (DB + CSB + CRPDB) * (k + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_finite_sched_changes_bounded_overheads_blackout
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (DB CSB CRPDB : Prosa_Behavior_Time_duration),
       Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job
         inst_3 sched DB CSB
         CRPDB ->
       forall (k : Nat) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Nat
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_3 sched
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
            t2)
         k ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Processor_Supply_blackout_during_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            sched t1 t2)
         (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) DB
                  CSB)
               CRPDB)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) k
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
```
