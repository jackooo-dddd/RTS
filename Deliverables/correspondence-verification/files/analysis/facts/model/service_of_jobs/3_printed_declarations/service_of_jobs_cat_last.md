# `service_of_jobs_cat_last`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_last`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_cat_last`
- Certificate: `service_of_jobs_cat_last_correspondence`

## Official Rocq

```coq
service_of_jobs_cat_last :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (P : pred (Equality.sort Job)) (js : seq (Equality.sort Job)) (t1 t2 : nat),
is_true (t1 <= t2) ->
@service_of_jobs Job PState sched P js t1 t2.+1 =
@service_of_jobs Job PState sched P js t1 t2 + @service_of_jobs_at Job PState sched P js t2

service_of_jobs_cat_last is not universe polymorphic
Arguments service_of_jobs_cat_last {Job PState} sched P js%seq_scope (t1 t2)%nat_scope _
service_of_jobs_cat_last is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_last
Declared in library prosa.analysis.facts.model.service_of_jobs, line 212, characters 8-32
@service_of_jobs_cat_last
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (P : pred (Equality.sort Job)) (js : seq (Equality.sort Job)) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       @service_of_jobs Job PState sched P js t1 t2.+1 =
       @service_of_jobs Job PState sched P js t1 t2 + @service_of_jobs_at Job PState sched P js t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_cat_last : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (js : List Job) (t1 t2 : ℕ),
  t1 ≤ t2 →
    Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P js t1 (t2 + 1) =
      Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P js t1 t2 +
        Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at sched P js t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_cat_last
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool) (js : List Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P js
            t1
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t2
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched P
               js t1 t2)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job
               inst_3 PState sched P
               js t2))
```
