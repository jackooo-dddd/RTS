# `arrivals_up_to_scheduled_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_up_to_scheduled_at`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_up_to_scheduled_at`
- Certificate: `arrivals_up_to_scheduled_at_correspondence`

## Official Rocq

```coq
arrivals_up_to_scheduled_at :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) ->
forall t' : nat, is_true (t <= t') -> is_true (j \in @arrivals_up_to Job arr_seq t')

arrivals_up_to_scheduled_at is not universe polymorphic
Arguments arrivals_up_to_scheduled_at {Job H PState} arr_seq H_arrival_times_are_consistent 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute j t H_scheduled_at 
  t'%nat_scope _
arrivals_up_to_scheduled_at is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_up_to_scheduled_at
Declared in library prosa.analysis.facts.behavior.arrivals, line 564, characters 8-35
@arrivals_up_to_scheduled_at
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) ->
       forall t' : nat, is_true (t <= t') -> is_true (j \in @arrivals_up_to Job arr_seq t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_up_to_scheduled_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
            Prosa.Behavior.Service.scheduled_at sched j t = true →
              ∀ (t' : ℕ), t ≤ t' → decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq t') = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_up_to_scheduled_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       forall t' : Nat,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t' ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
                  inst_3 arr_seq t')
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
                  inst_3 arr_seq t')))
         Bool_true
```
