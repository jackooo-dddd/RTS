# `service_is_zero_or_one`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.service_is_zero_or_one`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_is_zero_or_one`
- Certificate: `service_is_zero_or_one_correspondence`

## Official Rocq

```coq
service_is_zero_or_one :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
@service_at Job PState sched j t = 0 \/ @service_at Job PState sched j t = 1

service_is_zero_or_one is not universe polymorphic
Arguments service_is_zero_or_one {Job PState} H_unit_service sched j t
service_is_zero_or_one is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_is_zero_or_one
Declared in library prosa.analysis.facts.behavior.service, line 149, characters 12-34
@service_is_zero_or_one
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
       @service_at Job PState sched j t = 0 \/ @service_at Job PState sched j t = 1
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_is_zero_or_one : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.service_at sched j t = 0 ∨ Prosa.Behavior.Service.service_at sched j t = 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_is_zero_or_one
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       Or
         (@eq Prosa_Behavior_Job_work
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j t)
            (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
         (@eq Prosa_Behavior_Job_work
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j t)
            (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1)))
```
