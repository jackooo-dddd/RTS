# `no_service_not_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.no_service_not_scheduled`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.no_service_not_scheduled`
- Certificate: `no_service_not_scheduled_correspondence`

## Official Rocq

```coq
no_service_not_scheduled :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job),
@ideal_progress_proc_model Job PState ->
forall t : instant, is_true (~~ @scheduled_at Job PState sched j t) <-> @service_at Job PState sched j t = 0

no_service_not_scheduled is not universe polymorphic
Arguments no_service_not_scheduled {Job PState} sched j H_scheduled_implies_serviced t
no_service_not_scheduled is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.no_service_not_scheduled
Declared in library prosa.analysis.facts.behavior.service, line 440, characters 10-34
@no_service_not_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @ideal_progress_proc_model Job PState ->
       forall t : instant,
       is_true (~~ @scheduled_at Job PState sched j t) <-> @service_at Job PState sched j t = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.no_service_not_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    ∀ (t : Prosa.Behavior.Time.instant),
      (!Prosa.Behavior.Service.scheduled_at sched j t) = true ↔ Prosa.Behavior.Service.service_at sched j t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_no_service_not_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall t : Prosa_Behavior_Time_instant,
       Iff
         (@eq Bool
            (Bool_not
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched j t))
            Bool_true)
         (@eq Prosa_Behavior_Job_work
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j t)
            (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
```
