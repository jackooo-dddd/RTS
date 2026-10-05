# `service_during_first_plus_later`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_during_first_plus_later`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_during_first_plus_later`
- Certificate: `service_during_first_plus_later_correspondence`

## Official Rocq

```coq
service_during_first_plus_later :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : nat),
is_true (t1 < t2) ->
@service_at Job PState sched j t1 + @service_during Job PState sched j t1.+1 t2 =
@service_during Job PState sched j t1 t2

service_during_first_plus_later is not universe polymorphic
Arguments service_during_first_plus_later {Job PState} sched j (t1 t2)%nat_scope _
service_during_first_plus_later is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_during_first_plus_later
Declared in library prosa.analysis.facts.behavior.service, line 83, characters 8-39
@service_during_first_plus_later
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : nat),
       is_true (t1 < t2) ->
       @service_at Job PState sched j t1 + @service_during Job PState sched j t1.+1 t2 =
       @service_during Job PState sched j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_during_first_plus_later : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : ℕ),
  t1 < t2 →
    Prosa.Behavior.Service.service_at sched j t1 + Prosa.Behavior.Service.service_during sched j (t1 + 1) t2 =
      Prosa.Behavior.Service.service_during sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_during_first_plus_later
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Nat),
       LT_lt_inst1 Nat instLTNat t1 t2 ->
       @eq Prosa_Behavior_Job_work
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j t1)
            (Prosa_Behavior_Service_service_during Job
               inst_3 PState sched j
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t1
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
               t2))
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2)
```
