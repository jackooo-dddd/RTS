# `kth_scheduling_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.kth_scheduling_time`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.kth_scheduling_time`
- Certificate: `kth_scheduling_time_correspondence`

## Official Rocq

```coq
kth_scheduling_time :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t t' : instant) (k : nat),
@service Job PState sched j t = k ->
is_true (k < @service Job PState sched j t') ->
exists st : nat,
  is_true (t <= st < t') /\
  @service Job PState sched j st = k /\ is_true (@scheduled_at Job PState sched j st)

kth_scheduling_time is not universe polymorphic
Arguments kth_scheduling_time {Job PState} sched j t t' k%nat_scope _ _
kth_scheduling_time is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.kth_scheduling_time
Declared in library prosa.analysis.facts.behavior.service, line 839, characters 8-27
@kth_scheduling_time
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t t' : instant) (k : nat),
       @service Job PState sched j t = k ->
       is_true (k < @service Job PState sched j t') ->
       exists st : nat,
         is_true (t <= st < t') /\
         @service Job PState sched j st = k /\ is_true (@scheduled_at Job PState sched j st)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.kth_scheduling_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t t' : Prosa.Behavior.Time.instant) (k : ℕ),
  Prosa.Behavior.Service.service sched j t = k →
    k < Prosa.Behavior.Service.service sched j t' →
      ∃ st,
        (decide (t ≤ st) && decide (st < t')) = true ∧
          Prosa.Behavior.Service.service sched j st = k ∧ Prosa.Behavior.Service.scheduled_at sched j st = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_kth_scheduling_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t t' : Prosa_Behavior_Time_instant) (k : Nat),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
         k ->
       LT_lt_inst1 Nat instLTNat k
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t') ->
       Exists Nat
         (fun st : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t st) (Nat_decLe t st))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat st t') (Nat_decLt st t')))
               Bool_true)
            (And
               (@eq Prosa_Behavior_Job_work
                  (Prosa_Behavior_Service_service Job
                     inst_3 PState sched
                     j st)
                  k)
               (@eq Bool
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState sched
                     j st)
                  Bool_true)))
```
