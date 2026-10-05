# `service_of_jobs_pred0`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred0`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_pred0`
- Certificate: `service_of_jobs_pred0_correspondence`

## Official Rocq

```coq
service_of_jobs_pred0 :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
@service_of_jobs Job PState sched (pred_of_simpl (@pred0 (Equality.sort Job))) jobs t1 t2 = 0

service_of_jobs_pred0 is not universe polymorphic
Arguments service_of_jobs_pred0 {Job PState} sched jobs%seq_scope t1 t2
service_of_jobs_pred0 is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred0
Declared in library prosa.analysis.facts.model.service_of_jobs, line 168, characters 10-31
@service_of_jobs_pred0
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
       @service_of_jobs Job PState sched (pred_of_simpl (@pred0 (Equality.sort Job))) jobs t1 t2 = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_pred0 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (jobs : List Job) (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun x => false) jobs t1 t2 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_pred0
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched
            (fun _ : Job => Bool_false) jobs t1 t2)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
