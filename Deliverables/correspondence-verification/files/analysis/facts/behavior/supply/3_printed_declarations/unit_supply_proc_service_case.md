# `unit_supply_proc_service_case`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.supply.unit_supply_proc_service_case`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.unit_supply_proc_service_case`
- Certificate: `fs_unit_supply_proc_service_case_correspondence`

## Official Rocq

```coq
unit_supply_proc_service_case :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
@service_at Job PState sched j t = 0 \/ @service_at Job PState sched j t = 1

unit_supply_proc_service_case is not universe polymorphic
Arguments unit_supply_proc_service_case {Job PState} H_unit_supply_proc_model sched j t
unit_supply_proc_service_case is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.unit_supply_proc_service_case
Declared in library prosa.analysis.facts.behavior.supply, line 93, characters 12-41
@unit_supply_proc_service_case
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
       @service_at Job PState sched j t = 0 \/ @service_at Job PState sched j t = 1
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.unit_supply_proc_service_case : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.service_at sched j t = 0 ∨ Prosa.Behavior.Service.service_at sched j t = 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_unit_supply_proc_service_case
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
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
