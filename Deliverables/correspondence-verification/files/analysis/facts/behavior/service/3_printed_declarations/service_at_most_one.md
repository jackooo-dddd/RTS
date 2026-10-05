# `service_at_most_one`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_at_most_one`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_at_most_one`
- Certificate: `service_at_most_one_correspondence`

## Official Rocq

```coq
service_at_most_one :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
is_true (@service_at Job PState sched j t <= 1)

service_at_most_one is not universe polymorphic
Arguments service_at_most_one {Job PState} H_unit_service sched j t
service_at_most_one is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_at_most_one
Declared in library prosa.analysis.facts.behavior.service, line 144, characters 8-27
@service_at_most_one
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
       is_true (@service_at Job PState sched j t <= 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_at_most_one : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.service_at sched j t ≤ 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_at_most_one
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
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
```
