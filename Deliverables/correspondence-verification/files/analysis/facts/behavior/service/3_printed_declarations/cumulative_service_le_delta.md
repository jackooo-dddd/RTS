# `cumulative_service_le_delta`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.cumulative_service_le_delta`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.cumulative_service_le_delta`
- Certificate: `cumulative_service_le_delta_correspondence`

## Official Rocq

```coq
cumulative_service_le_delta :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant) (delta : nat),
is_true (@service_during Job PState sched j t (t + delta) <= delta)

cumulative_service_le_delta is not universe polymorphic
Arguments cumulative_service_le_delta {Job PState} H_unit_service sched j t delta%nat_scope
cumulative_service_le_delta is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.cumulative_service_le_delta
Declared in library prosa.analysis.facts.behavior.service, line 158, characters 8-35
@cumulative_service_le_delta
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant) (delta : nat),
       is_true (@service_during Job PState sched j t (t + delta) <= delta)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.cumulative_service_le_delta : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant) (delta : ℕ),
      Prosa.Behavior.Service.service_during sched j t (t + delta) ≤ delta
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_cumulative_service_le_delta
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant) (delta : Nat),
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
               (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t delta))
         delta
```
