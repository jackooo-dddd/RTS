# `service_monotonic`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_monotonic`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_monotonic`
- Certificate: `service_monotonic_correspondence`

## Official Rocq

```coq
service_monotonic :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : nat),
is_true (t1 <= t2) -> is_true (@service Job PState sched j t1 <= @service Job PState sched j t2)

service_monotonic is not universe polymorphic
Arguments service_monotonic {Job PState} sched j (t1 t2)%nat_scope _
service_monotonic is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_monotonic
Declared in library prosa.analysis.facts.behavior.service, line 281, characters 8-25
@service_monotonic
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : nat),
       is_true (t1 <= t2) -> is_true (@service Job PState sched j t1 <= @service Job PState sched j t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_monotonic : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t1 t2 : ℕ), t1 ≤ t2 → Prosa.Behavior.Service.service sched j t1 ≤ Prosa.Behavior.Service.service sched j t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_monotonic
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t1)
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t2)
```
