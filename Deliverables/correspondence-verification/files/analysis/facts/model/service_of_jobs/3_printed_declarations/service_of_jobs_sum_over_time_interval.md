# `service_of_jobs_sum_over_time_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_sum_over_time_interval`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_sum_over_time_interval`
- Certificate: `service_of_jobs_sum_over_time_interval_correspondence`

## Official Rocq

```coq
service_of_jobs_sum_over_time_interval :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
@service_of_jobs Job PState sched P jobs t1 t2 =
\sum_(t1 <= t < t2) @service_of_jobs_at Job PState sched P jobs t

service_of_jobs_sum_over_time_interval is not universe polymorphic
Arguments service_of_jobs_sum_over_time_interval {Job PState} sched P jobs%seq_scope t1 t2
service_of_jobs_sum_over_time_interval is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_sum_over_time_interval
Declared in library prosa.analysis.facts.model.service_of_jobs, line 162, characters 10-48
@service_of_jobs_sum_over_time_interval
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
       @service_of_jobs Job PState sched P jobs t1 t2 =
       \sum_(t1 <= t < t2) @service_of_jobs_at Job PState sched P jobs t
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_sum_over_time_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (jobs : List Job)
  (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P jobs t1 t2 =
    ∑ t ∈ Finset.Ico t1 t2, Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at sched P jobs t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_sum_over_time_interval
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool) (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P jobs
            t1 t2)
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat
               (fun t : Nat =>
                Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job
                  inst_3 PState sched
                  P jobs t)
               (List_range' t1 (Nat_sub t2 t1) 1)))
```
