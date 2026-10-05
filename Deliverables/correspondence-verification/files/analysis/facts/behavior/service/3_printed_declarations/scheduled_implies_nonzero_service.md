# `scheduled_implies_nonzero_service`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.scheduled_implies_nonzero_service`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.scheduled_implies_nonzero_service`
- Certificate: `scheduled_implies_nonzero_service_correspondence`

## Official Rocq

```coq
scheduled_implies_nonzero_service :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job),
@ideal_progress_proc_model Job PState ->
forall t : nat,
(exists t' : nat, is_true (t' < t) /\ is_true (@scheduled_at Job PState sched j t')) ->
is_true (0 < @service Job PState sched j t)

scheduled_implies_nonzero_service is not universe polymorphic
Arguments scheduled_implies_nonzero_service {Job PState} sched j H_scheduled_implies_serviced t%nat_scope _
scheduled_implies_nonzero_service is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.scheduled_implies_nonzero_service
Declared in library prosa.analysis.facts.behavior.service, line 474, characters 14-47
@scheduled_implies_nonzero_service
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @ideal_progress_proc_model Job PState ->
       forall t : nat,
       (exists t' : nat, is_true (t' < t) /\ is_true (@scheduled_at Job PState sched j t')) ->
       is_true (0 < @service Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.scheduled_implies_nonzero_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    ∀ (t : ℕ),
      (∃ t' < t, Prosa.Behavior.Service.scheduled_at sched j t' = true) → 0 < Prosa.Behavior.Service.service sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_scheduled_implies_nonzero_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall t : Nat,
       Exists Nat
         (fun t' : Nat =>
          And (LT_lt_inst1 Nat instLTNat t' t)
            (@eq Bool
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched j t')
               Bool_true)) ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
```
