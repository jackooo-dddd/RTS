# `unit_service_at1`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.unit_service_at1`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.unit_service_at1`
- Certificate: `unit_service_at1_correspondence`

## Official Rocq

```coq
unit_service_at1 :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job),
@ideal_progress_proc_model Job PState ->
@unit_service_proc_model Job PState ->
forall t : instant, is_true (@scheduled_at Job PState sched j t) -> @service_at Job PState sched j t = 1

unit_service_at1 is not universe polymorphic
Arguments unit_service_at1 {Job PState} sched j H_scheduled_implies_serviced H_unit t _
unit_service_at1 is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.unit_service_at1
Declared in library prosa.analysis.facts.behavior.service, line 487, characters 10-26
@unit_service_at1
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @ideal_progress_proc_model Job PState ->
       @unit_service_proc_model Job PState ->
       forall t : instant,
       is_true (@scheduled_at Job PState sched j t) -> @service_at Job PState sched j t = 1
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.unit_service_at1 : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      ∀ (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Service.service_at sched j t = 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_unit_service_at1
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
```
