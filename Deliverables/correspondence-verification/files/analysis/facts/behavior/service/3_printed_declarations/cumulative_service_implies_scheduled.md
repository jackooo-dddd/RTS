# `cumulative_service_implies_scheduled`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.cumulative_service_implies_scheduled`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.cumulative_service_implies_scheduled`
- Certificate: `cumulative_service_implies_scheduled_correspondence`

## Official Rocq

```coq
cumulative_service_implies_scheduled :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : instant),
is_true (0 < @service_during Job PState sched j t1 t2) ->
exists t : nat, is_true (t1 <= t < t2) /\ is_true (@scheduled_at Job PState sched j t)

cumulative_service_implies_scheduled is not universe polymorphic
Arguments cumulative_service_implies_scheduled {Job PState} sched j t1 t2 _
cumulative_service_implies_scheduled is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.cumulative_service_implies_scheduled
Declared in library prosa.analysis.facts.behavior.service, line 372, characters 12-48
@cumulative_service_implies_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       is_true (0 < @service_during Job PState sched j t1 t2) ->
       exists t : nat, is_true (t1 <= t < t2) /\ is_true (@scheduled_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.cumulative_service_implies_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  0 < Prosa.Behavior.Service.service_during sched j t1 t2 →
    ∃ t, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ Prosa.Behavior.Service.scheduled_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_cumulative_service_implies_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2) ->
       Exists Nat
         (fun t : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
               Bool_true)
            (@eq Bool
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched j t)
               Bool_true))
```
