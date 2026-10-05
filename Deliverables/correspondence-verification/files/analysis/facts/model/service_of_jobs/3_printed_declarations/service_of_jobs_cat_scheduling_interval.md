# `service_of_jobs_cat_scheduling_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_scheduling_interval`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_cat_scheduling_interval`
- Certificate: `service_of_jobs_cat_scheduling_interval_correspondence`

## Official Rocq

```coq
service_of_jobs_cat_scheduling_interval :
forall {Job : JobType} {H0 : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H0 PState sched ->
forall (P : pred (Equality.sort Job)) (t1 t2 t : nat),
is_true (t1 <= t <= t2) ->
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t2) t1 t2 =
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t1 t +
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t t2 +
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t t2) t t2

service_of_jobs_cat_scheduling_interval is not universe polymorphic
Arguments service_of_jobs_cat_scheduling_interval {Job H0 PState} arr_seq H_arrival_times_are_consistent
  sched H_jobs_must_arrive_to_execute P (t1 t2 t)%nat_scope _
service_of_jobs_cat_scheduling_interval is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_scheduling_interval
Declared in library prosa.analysis.facts.model.service_of_jobs, line 45, characters 8-47
@service_of_jobs_cat_scheduling_interval
     : forall (Job : JobType) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       forall (P : pred (Equality.sort Job)) (t1 t2 t : nat),
       is_true (t1 <= t <= t2) ->
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t2) t1 t2 =
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t1 t +
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t t2 +
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t t2) t t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_cat_scheduling_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
        ∀ (P : Job → Bool) (t1 t2 t : ℕ),
          (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
            Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) t1 t2 =
              Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t) t1 t +
                  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t) t t2 +
                Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
                  (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t t2) t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_cat_scheduling_interval
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
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall (P : Job -> Bool) (t1 t2 t : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LE_le_inst1 Nat instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2)
            t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
               (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
                  inst_3 PState sched
                  P
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_3 arr_seq t1
                     t)
                  t1 t)
               (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
                  inst_3 PState sched
                  P
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_3 arr_seq t1
                     t)
                  t t2))
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched P
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t t2)
               t t2))
```
