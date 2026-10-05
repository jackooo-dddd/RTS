# `service_of_jobs_negate_pred`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_negate_pred`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_negate_pred`
- Certificate: `service_of_jobs_negate_pred_correspondence`

## Official Rocq

```coq
service_of_jobs_negate_pred :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
@service_of_jobs Job PState sched P jobs t1 t2 =
@total_service_of_jobs_in Job PState sched jobs t1 t2 -
@service_of_jobs Job PState sched (fun j : Equality.sort Job => ~~ P j) jobs t1 t2

service_of_jobs_negate_pred is not universe polymorphic
Arguments service_of_jobs_negate_pred {Job PState} sched P jobs%seq_scope t1 t2
service_of_jobs_negate_pred is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_negate_pred
Declared in library prosa.analysis.facts.model.service_of_jobs, line 119, characters 10-37
@service_of_jobs_negate_pred
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
       @service_of_jobs Job PState sched P jobs t1 t2 =
       @total_service_of_jobs_in Job PState sched jobs t1 t2 -
       @service_of_jobs Job PState sched (fun j : Equality.sort Job => ~~ P j) jobs t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_negate_pred : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (jobs : List Job)
  (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P jobs t1 t2 =
    Prosa.Model.Aggregate.ServiceOfJobs.total_service_of_jobs_in sched jobs t1 t2 -
      Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun j => !P j) jobs t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_negate_pred
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
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in Job
               inst_3 PState sched jobs
               t1 t2)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched
               (fun j : Job => Bool_not (P j)) jobs t1 t2))
```
