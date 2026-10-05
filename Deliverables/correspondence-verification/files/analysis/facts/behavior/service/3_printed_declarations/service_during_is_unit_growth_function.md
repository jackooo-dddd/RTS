# `service_during_is_unit_growth_function`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_during_is_unit_growth_function`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_during_is_unit_growth_function`
- Certificate: `service_during_is_unit_growth_function_correspondence`

## Official Rocq

```coq
service_during_is_unit_growth_function :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t0 : instant),
unit_growth_function (@service_during Job PState sched j t0)

service_during_is_unit_growth_function is not universe polymorphic
Arguments service_during_is_unit_growth_function {Job PState} H_unit_service sched j t0 t
service_during_is_unit_growth_function is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_during_is_unit_growth_function
Declared in library prosa.analysis.facts.behavior.service, line 178, characters 10-48
@service_during_is_unit_growth_function
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t0 : instant),
       unit_growth_function (@service_during Job PState sched j t0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_during_is_unit_growth_function : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t0 : Prosa.Behavior.Time.instant),
      Prosa.Util.UnitGrowth.unit_growth_function (Prosa.Behavior.Service.service_during sched j t0)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_during_is_unit_growth_function
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t0 : Prosa_Behavior_Time_instant),
       Prosa_Util_UnitGrowth_unit_growth_function
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t0)
```
