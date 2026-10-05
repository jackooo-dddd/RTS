# `positive_service_implies_scheduled_since_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_since_arrival`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_since_arrival`
- Certificate: `positive_service_implies_scheduled_since_arrival_correspondence`

## Official Rocq

```coq
positive_service_implies_scheduled_since_arrival :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) {H : JobArrival Job},
@jobs_must_arrive_to_execute Job H PState sched ->
forall t : instant,
is_true (0 < @service Job PState sched j t) ->
exists t' : nat, is_true (@job_arrival Job H j <= t' < t) /\ is_true (@scheduled_at Job PState sched j t')

positive_service_implies_scheduled_since_arrival is not universe polymorphic
Arguments positive_service_implies_scheduled_since_arrival {Job PState} sched j {H} H_jobs_must_arrive t _
positive_service_implies_scheduled_since_arrival is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_since_arrival
Declared in library prosa.analysis.facts.behavior.service, line 517, characters 10-58
@positive_service_implies_scheduled_since_arrival
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (H : JobArrival Job),
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall t : instant,
       is_true (0 < @service Job PState sched j t) ->
       exists t' : nat,
         is_true (@job_arrival Job H j <= t' < t) /\ is_true (@scheduled_at Job PState sched j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_since_arrival : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (t : Prosa.Behavior.Time.instant),
      0 < Prosa.Behavior.Service.service sched j t →
        ∃ t',
          (decide (Prosa.Behavior.Job.job_arrival j ≤ t') && decide (t' < t)) = true ∧
            Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_positive_service_implies_scheduled_since_arrival
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job)
         (inst_11 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_11 PState sched ->
       forall t : Prosa_Behavior_Time_instant,
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t) ->
       Exists Nat
         (fun t' : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_11 j)
                        t')
                     (Nat_decLe
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_11 j)
                        t'))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat t' t) (Nat_decLt t' t)))
               Bool_true)
            (@eq Bool
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched j
                  t')
               Bool_true))
```
