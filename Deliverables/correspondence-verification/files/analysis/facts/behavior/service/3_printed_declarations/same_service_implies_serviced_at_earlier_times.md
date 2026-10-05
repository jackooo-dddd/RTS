# `same_service_implies_serviced_at_earlier_times`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.same_service_implies_serviced_at_earlier_times`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.same_service_implies_serviced_at_earlier_times`
- Certificate: `same_service_implies_serviced_at_earlier_times_correspondence`

## Official Rocq

```coq
same_service_implies_serviced_at_earlier_times :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : instant),
is_true (t1 <= t2) ->
@service Job PState sched j t1 = @service Job PState sched j t2 ->

same_service_implies_serviced_at_earlier_times is not universe polymorphic
Arguments same_service_implies_serviced_at_earlier_times {Job PState} sched j t1 t2 H_t1_le_t2 H_same_service
same_service_implies_serviced_at_earlier_times is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.same_service_implies_serviced_at_earlier_times
Declared in library prosa.analysis.facts.behavior.service, line 603, characters 10-56
@same_service_implies_serviced_at_earlier_times
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       @service Job PState sched j t1 = @service Job PState sched j t2 ->
       [exists t, 0 < @service_at Job PState sched j (@nat_of_ord t1 t)] =
       [exists t', 0 < @service_at Job PState sched j (@nat_of_ord t2 t')]
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.same_service_implies_serviced_at_earlier_times : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    Prosa.Behavior.Service.service sched j t1 = Prosa.Behavior.Service.service sched j t2 →
      ((List.range' 0 t1).any fun t => decide (0 < Prosa.Behavior.Service.service_at sched j t)) =
        (List.range' 0 t2).any fun t => decide (0 < Prosa.Behavior.Service.service_at sched j t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_same_service_implies_serviced_at_earlier_times
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
       @eq Bool
         (List_any_inst1 Nat
            (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) t1
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (fun t : Nat =>
             Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
                  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
                  (Prosa_Behavior_Service_service_at Job
                     inst_3 PState sched
                     j t))
               (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
                  (Prosa_Behavior_Service_service_at Job
                     inst_3 PState sched
                     j t))))
         (List_any_inst1 Nat
            (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) t2
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (fun t : Nat =>
             Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
                  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
                  (Prosa_Behavior_Service_service_at Job
                     inst_3 PState sched
                     j t))
               (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
                  (Prosa_Behavior_Service_service_at Job
                     inst_3 PState sched
                     j t))))
```
