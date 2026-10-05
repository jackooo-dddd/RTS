# `service_in_replaced`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.transform.replace_at.service_in_replaced`
- Lean: `Prosa.Analysis.Facts.Transform.ReplaceAt.service_in_replaced`
- Certificate: `service_in_replaced_correspondence`

## Official Rocq

```coq
service_in_replaced :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t' : instant) (nstate : @State Job PState) (t1 t2 : nat),
is_true (t1 <= t' < t2) ->
forall j : Equality.sort Job,
@service_during Job PState (@replace_at Job PState sched t' nstate) j t1 t2 =
@service_during Job PState sched j t1 t2 +
@service_at Job PState (@replace_at Job PState sched t' nstate) j t' - @service_at Job PState sched j t'

service_in_replaced is not universe polymorphic
Arguments service_in_replaced {Job PState} sched t' nstate (t1 t2)%nat_scope _ j
service_in_replaced is opaque
Expands to: Constant prosa.analysis.facts.transform.replace_at.service_in_replaced
Declared in library prosa.analysis.facts.transform.replace_at, line 79, characters 12-31
@service_in_replaced
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t' : instant) (nstate : @State Job PState) (t1 t2 : nat),
       is_true (t1 <= t' < t2) ->
       forall j : Equality.sort Job,
       @service_during Job PState (@replace_at Job PState sched t' nstate) j t1 t2 =
       @service_during Job PState sched j t1 t2 +
       @service_at Job PState (@replace_at Job PState sched t' nstate) j t' -
       @service_at Job PState sched j t'
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.ReplaceAt.service_in_replaced : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t' : Prosa.Behavior.Time.instant)
  (nstate : Prosa.Behavior.Schedule.ProcessorState.State Job) (t1 t2 : ℕ),
  (decide (t1 ≤ t') && decide (t' < t2)) = true →
    ∀ (j : Job),
      Prosa.Behavior.Service.service_during (Prosa.Analysis.Transform.Swap.replace_at sched t' nstate) j t1 t2 =
        Prosa.Behavior.Service.service_during sched j t1 t2 +
            Prosa.Behavior.Service.service_at (Prosa.Analysis.Transform.Swap.replace_at sched t' nstate) j t' -
          Prosa.Behavior.Service.service_at sched j t'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_ReplaceAt_service_in_replaced
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t' : Prosa_Behavior_Time_instant)
         (nstate : Prosa_Behavior_Schedule_ProcessorState_State Job
                     inst_3 PState)
         (t1 t2 : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t') (Nat_decLe t1 t'))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t' t2) (Nat_decLt t' t2)))
         Bool_true ->
       forall j : Job,
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_replace_at Job
               inst_3 PState sched t'
               nstate)
            j t1 t2)
         (HSub_hSub_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
            (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
            (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
               (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
               (Prosa_Behavior_Service_service_during Job
                  inst_3 PState sched
                  j t1 t2)
               (Prosa_Behavior_Service_service_at Job
                  inst_3 PState
                  (Prosa_Analysis_Transform_Swap_replace_at Job
                     inst_3 PState
                     sched t' nstate)
                  j t'))
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j
               t'))
```
