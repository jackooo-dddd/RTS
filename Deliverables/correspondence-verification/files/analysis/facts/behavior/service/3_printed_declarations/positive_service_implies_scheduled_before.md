# `positive_service_implies_scheduled_before`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_before`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_before`
- Certificate: `positive_service_implies_scheduled_before_correspondence`

## Official Rocq

```coq
positive_service_implies_scheduled_before :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (0 < @service Job PState sched j t) ->
exists t' : nat, is_true (t' < t) /\ is_true (@scheduled_at Job PState sched j t')

positive_service_implies_scheduled_before is not universe polymorphic
Arguments positive_service_implies_scheduled_before {Job PState} sched j t _
positive_service_implies_scheduled_before is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_before
Declared in library prosa.analysis.facts.behavior.service, line 385, characters 12-53
@positive_service_implies_scheduled_before
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (0 < @service Job PState sched j t) ->
       exists t' : nat, is_true (t' < t) /\ is_true (@scheduled_at Job PState sched j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  0 < Prosa.Behavior.Service.service sched j t → ∃ t' < t, Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_positive_service_implies_scheduled_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t) ->
       Exists Nat
         (fun t' : Nat =>
          And (LT_lt_inst1 Nat instLTNat t' t)
            (@eq Bool
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched j
                  t')
               Bool_true))
```
