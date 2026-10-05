# `service_of_jobs_cat_arrival_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_arrival_interval`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_cat_arrival_interval`
- Certificate: `service_of_jobs_cat_arrival_interval_correspondence`

## Official Rocq

```coq
service_of_jobs_cat_arrival_interval :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (t1 t2 t : nat),
is_true (t1 <= t <= t2) ->
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t2) t t2 =
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t t2 +
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t t2) t t2

service_of_jobs_cat_arrival_interval is not universe polymorphic
Arguments service_of_jobs_cat_arrival_interval {Job PState} arr_seq sched P (t1 t2 t)%nat_scope _
service_of_jobs_cat_arrival_interval is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_arrival_interval
Declared in library prosa.analysis.facts.model.service_of_jobs, line 74, characters 8-44
@service_of_jobs_cat_arrival_interval
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (t1 t2 t : nat),
       is_true (t1 <= t <= t2) ->
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t2) t t2 =
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t t2 +
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t t2) t t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_cat_arrival_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (P : Job → Bool) (t1 t2 t : ℕ),
  (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
    Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
        (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) t t2 =
      Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t) t t2 +
        Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t t2) t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_cat_arrival_interval
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool) (t1 t2 t : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LE_le_inst1 Nat instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2)
            t t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched P
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t)
               t t2)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched P
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t t2)
               t t2))
```
