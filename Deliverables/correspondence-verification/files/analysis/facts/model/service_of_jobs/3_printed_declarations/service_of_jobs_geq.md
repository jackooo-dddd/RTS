# `service_of_jobs_geq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_geq`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_geq`
- Certificate: `service_of_jobs_geq_correspondence`

## Official Rocq

```coq
service_of_jobs_geq :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
is_true (t2 <= t1) -> @service_of_jobs Job PState sched P jobs t1 t2 = 0

service_of_jobs_geq is not universe polymorphic
Arguments service_of_jobs_geq {Job PState} sched P jobs%seq_scope t1 t2 _
service_of_jobs_geq is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_geq
Declared in library prosa.analysis.facts.model.service_of_jobs, line 195, characters 10-29
@service_of_jobs_geq
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
       is_true (t2 <= t1) -> @service_of_jobs Job PState sched P jobs t1 t2 = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_geq : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (jobs : List Job)
  (t1 t2 : Prosa.Behavior.Time.instant),
  t2 ≤ t1 → Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P jobs t1 t2 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_geq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool) (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t2 t1 ->
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P jobs
            t1 t2)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
