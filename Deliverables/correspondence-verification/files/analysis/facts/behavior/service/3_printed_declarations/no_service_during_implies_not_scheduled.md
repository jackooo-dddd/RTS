# `no_service_during_implies_not_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.no_service_during_implies_not_scheduled`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.no_service_during_implies_not_scheduled`
- Certificate: `no_service_during_implies_not_scheduled_correspondence`

## Official Rocq

```coq
no_service_during_implies_not_scheduled :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job),
@ideal_progress_proc_model Job PState ->
forall t1 t2 : instant,
@service_during Job PState sched j t1 t2 = 0 ->
forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ @scheduled_at Job PState sched j t)

no_service_during_implies_not_scheduled is not universe polymorphic
Arguments no_service_during_implies_not_scheduled {Job PState} sched j H_scheduled_implies_serviced 
  t1 t2 _ t%nat_scope _
no_service_during_implies_not_scheduled is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.no_service_during_implies_not_scheduled
Declared in library prosa.analysis.facts.behavior.service, line 452, characters 10-49
@no_service_during_implies_not_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @ideal_progress_proc_model Job PState ->
       forall t1 t2 : instant,
       @service_during Job PState sched j t1 t2 = 0 ->
       forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ @scheduled_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.no_service_during_implies_not_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.service_during sched j t1 t2 = 0 →
        ∀ (t : ℕ), (decide (t1 ≤ t) && decide (t < t2)) = true → (!Prosa.Behavior.Service.scheduled_at sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_no_service_during_implies_not_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)) ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j t))
         Bool_true
```
