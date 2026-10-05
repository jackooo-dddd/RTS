# `service_of_jobs_pred_impl`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred_impl`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_pred_impl`
- Certificate: `service_of_jobs_pred_impl_correspondence`

## Official Rocq

```coq
service_of_jobs_pred_impl :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (jobs : seq (Equality.sort Job)) (t1 t2 : instant) (P1 P2 : pred (Equality.sort Job)),
(forall j : Equality.sort Job, is_true (j \in jobs) -> is_true (P1 j) -> is_true (P2 j)) ->
is_true (@service_of_jobs Job PState sched P1 jobs t1 t2 <= @service_of_jobs Job PState sched P2 jobs t1 t2)

service_of_jobs_pred_impl is not universe polymorphic
Arguments service_of_jobs_pred_impl {Job PState} sched jobs%seq_scope t1 t2 P1 P2 _%function_scope
service_of_jobs_pred_impl is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred_impl
Declared in library prosa.analysis.facts.model.service_of_jobs, line 134, characters 10-35
@service_of_jobs_pred_impl
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (jobs : seq (Equality.sort Job)) (t1 t2 : instant) (P1 P2 : pred (Equality.sort Job)),
       (forall j : Equality.sort Job, is_true (j \in jobs) -> is_true (P1 j) -> is_true (P2 j)) ->
       is_true
         (@service_of_jobs Job PState sched P1 jobs t1 t2 <= @service_of_jobs Job PState sched P2 jobs t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_pred_impl : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (jobs : List Job) (t1 t2 : Prosa.Behavior.Time.instant)
  (P1 P2 : Job → Bool),
  (∀ (j : Job), decide (j ∈ jobs) = true → P1 j = true → P2 j = true) →
    Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P1 jobs t1 t2 ≤
      Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P2 jobs t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_pred_impl
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant) (P1 P2 : Job -> Bool),
       (forall j : Job,
        @eq Bool
          (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) jobs j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_3)
                (instLawfulBEq Job
                   inst_3)
                j jobs))
          Bool_true ->
        @eq Bool (P1 j) Bool_true -> @eq Bool (P2 j) Bool_true) ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P1
            jobs t1 t2)
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P2
            jobs t1 t2)
```
