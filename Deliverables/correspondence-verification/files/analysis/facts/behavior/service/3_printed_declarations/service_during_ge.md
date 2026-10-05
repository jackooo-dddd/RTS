# `service_during_ge`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.service_during_ge`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_during_ge`
- Certificate: `service_during_ge_correspondence`

## Official Rocq

```coq
service_during_ge :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : instant) (k : nat),
is_true (k < @service_during Job PState sched j t1 t2) -> is_true (t1 < t2)

service_during_ge is not universe polymorphic
Arguments service_during_ge {Job PState} sched j t1 t2 k%nat_scope _
service_during_ge is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_during_ge
Declared in library prosa.analysis.facts.behavior.service, line 39, characters 12-29
@service_during_ge
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant) (k : nat),
       is_true (k < @service_during Job PState sched j t1 t2) -> is_true (t1 < t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_during_ge : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t1 t2 : Prosa.Behavior.Time.instant), ∀ k < Prosa.Behavior.Service.service_during sched j t1 t2, t1 < t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_during_ge
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) (k : Nat),
       LT_lt_inst1 Nat instLTNat k
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2) ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t2
```
