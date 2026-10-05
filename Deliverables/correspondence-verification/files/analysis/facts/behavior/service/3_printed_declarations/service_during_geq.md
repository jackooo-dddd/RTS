# `service_during_geq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_during_geq`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_during_geq`
- Certificate: `service_during_geq_correspondence`

## Official Rocq

```coq
service_during_geq :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : nat),
is_true (t2 <= t1) -> @service_during Job PState sched j t1 t2 = 0

service_during_geq is not universe polymorphic
Arguments service_during_geq {Job PState} sched j (t1 t2)%nat_scope _
service_during_geq is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_during_geq
Declared in library prosa.analysis.facts.behavior.service, line 32, characters 8-26
@service_during_geq
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : nat),
       is_true (t2 <= t1) -> @service_during Job PState sched j t1 t2 = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_during_geq : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : ℕ),
  t2 ≤ t1 → Prosa.Behavior.Service.service_during sched j t1 t2 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_during_geq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t2 t1 ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
