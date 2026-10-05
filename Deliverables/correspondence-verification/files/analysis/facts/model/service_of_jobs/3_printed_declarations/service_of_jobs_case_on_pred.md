# `service_of_jobs_case_on_pred`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_case_on_pred`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_case_on_pred`
- Certificate: `service_of_jobs_case_on_pred_correspondence`

## Official Rocq

```coq
service_of_jobs_case_on_pred :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (jobs : seq (Equality.sort Job)) (t1 t2 : instant) (P1 P2 : pred (Equality.sort Job)),
@service_of_jobs Job PState sched P1 jobs t1 t2 =
@service_of_jobs Job PState sched (fun j : Equality.sort Job => P1 j && P2 j) jobs t1 t2 +
@service_of_jobs Job PState sched (fun j : Equality.sort Job => P1 j && ~~ P2 j) jobs t1 t2

service_of_jobs_case_on_pred is not universe polymorphic
Arguments service_of_jobs_case_on_pred {Job PState} sched jobs%seq_scope t1 t2 P1 P2
service_of_jobs_case_on_pred is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_case_on_pred
Declared in library prosa.analysis.facts.model.service_of_jobs, line 104, characters 10-38
@service_of_jobs_case_on_pred
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (jobs : seq (Equality.sort Job)) (t1 t2 : instant) (P1 P2 : pred (Equality.sort Job)),
       @service_of_jobs Job PState sched P1 jobs t1 t2 =
       @service_of_jobs Job PState sched (fun j : Equality.sort Job => P1 j && P2 j) jobs t1 t2 +
       @service_of_jobs Job PState sched (fun j : Equality.sort Job => P1 j && ~~ P2 j) jobs t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_case_on_pred : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (jobs : List Job) (t1 t2 : Prosa.Behavior.Time.instant)
  (P1 P2 : Job → Bool),
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P1 jobs t1 t2 =
    Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun j => P1 j && P2 j) jobs t1 t2 +
      Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun j => P1 j && !P2 j) jobs t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_case_on_pred
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant) (P1 P2 : Job -> Bool),
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P1
            jobs t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched
               (fun j : Job => Bool_and (P1 j) (P2 j)) jobs t1 t2)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
               inst_3 PState sched
               (fun j : Job => Bool_and (P1 j) (Bool_not (P2 j))) jobs t1 t2))
```
