# `constant_service_implies_no_service_during`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.constant_service_implies_no_service_during`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_no_service_during`
- Certificate: `constant_service_implies_no_service_during_correspondence`

## Official Rocq

```coq
constant_service_implies_no_service_during :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : instant),
is_true (t1 <= t2) ->
@service Job PState sched j t1 = @service Job PState sched j t2 ->
@service_during Job PState sched j t1 t2 = 0

constant_service_implies_no_service_during is not universe polymorphic
Arguments constant_service_implies_no_service_during {Job PState} sched j t1 t2 H_t1_le_t2 H_same_service
constant_service_implies_no_service_during is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.constant_service_implies_no_service_during
Declared in library prosa.analysis.facts.behavior.service, line 583, characters 10-52
@constant_service_implies_no_service_during
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       @service Job PState sched j t1 = @service Job PState sched j t2 ->
       @service_during Job PState sched j t1 t2 = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_no_service_during : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    Prosa.Behavior.Service.service sched j t1 = Prosa.Behavior.Service.service sched j t2 →
      Prosa.Behavior.Service.service_during sched j t1 t2 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_constant_service_implies_no_service_during
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t1)
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t2) ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
