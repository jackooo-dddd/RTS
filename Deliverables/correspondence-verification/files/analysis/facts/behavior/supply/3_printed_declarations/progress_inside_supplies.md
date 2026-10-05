# `progress_inside_supplies`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.progress_inside_supplies`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.progress_inside_supplies`
- Certificate: `fs_progress_inside_supplies_correspondence`

## Official Rocq

```coq
progress_inside_supplies :
forall {Job : JobType} {PState : ProcessorState Job},
@fully_consuming_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
is_true (@has_supply Job PState sched t) ->
is_true (@scheduled_at Job PState sched j t) -> is_true (0 < @service_at Job PState sched j t)

progress_inside_supplies is not universe polymorphic
Arguments progress_inside_supplies {Job PState} H_supply_is_fully_consumed sched j t _ _
progress_inside_supplies is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.progress_inside_supplies
Declared in library prosa.analysis.facts.behavior.supply, line 212, characters 8-32
@progress_inside_supplies
     : forall (Job : JobType) (PState : ProcessorState Job),
       @fully_consuming_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
       is_true (@has_supply Job PState sched t) ->
       is_true (@scheduled_at Job PState sched j t) -> is_true (0 < @service_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.progress_inside_supplies : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Model.Processor.Supply.has_supply sched t = true →
        Prosa.Behavior.Service.scheduled_at sched j t = true → 0 < Prosa.Behavior.Service.service_at sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_progress_inside_supplies
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_3 PState ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Supply_has_supply Job
            inst_3 PState sched t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
```
