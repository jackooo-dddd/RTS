# `service_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_cat`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_cat`
- Certificate: `service_cat_correspondence`

## Official Rocq

```coq
service_cat :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : nat),
is_true (t1 <= t2) ->
@service Job PState sched j t1 + @service_during Job PState sched j t1 t2 = @service Job PState sched j t2

service_cat is not universe polymorphic
Arguments service_cat {Job PState} sched j (t1 t2)%nat_scope _
service_cat is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_cat
Declared in library prosa.analysis.facts.behavior.service, line 74, characters 8-19
@service_cat
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       @service Job PState sched j t1 + @service_during Job PState sched j t1 t2 =
       @service Job PState sched j t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_cat : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t1 t2 : ℕ),
  t1 ≤ t2 →
    Prosa.Behavior.Service.service sched j t1 + Prosa.Behavior.Service.service_during sched j t1 t2 =
      Prosa.Behavior.Service.service sched j t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       @eq Prosa_Behavior_Job_work
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Behavior_Service_service Job
               inst_3 PState sched j t1)
            (Prosa_Behavior_Service_service_during Job
               inst_3 PState sched j t1
               t2))
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t2)
```
