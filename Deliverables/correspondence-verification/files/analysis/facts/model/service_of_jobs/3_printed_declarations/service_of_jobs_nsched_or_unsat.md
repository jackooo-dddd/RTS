# `service_of_jobs_nsched_or_unsat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_nsched_or_unsat`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_nsched_or_unsat`
- Certificate: `service_of_jobs_nsched_or_unsat_correspondence`

## Official Rocq

```coq
service_of_jobs_nsched_or_unsat :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t : instant),
(forall j : Equality.sort Job,
 is_true (j \in jobs) -> is_true (~~ (P j && @scheduled_at Job PState sched j t))) ->
@service_of_jobs_at Job PState sched P jobs t = 0

service_of_jobs_nsched_or_unsat is not universe polymorphic
Arguments service_of_jobs_nsched_or_unsat {Job PState} sched P jobs%seq_scope t _%function_scope
service_of_jobs_nsched_or_unsat is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_nsched_or_unsat
Declared in library prosa.analysis.facts.model.service_of_jobs, line 175, characters 10-41
@service_of_jobs_nsched_or_unsat
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t : instant),
       (forall j : Equality.sort Job,
        is_true (j \in jobs) -> is_true (~~ (P j && @scheduled_at Job PState sched j t))) ->
       @service_of_jobs_at Job PState sched P jobs t = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_nsched_or_unsat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (jobs : List Job)
  (t : Prosa.Behavior.Time.instant),
  (∀ (j : Job), decide (j ∈ jobs) = true → (!(P j && Prosa.Behavior.Service.scheduled_at sched j t)) = true) →
    Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at sched P jobs t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_nsched_or_unsat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool) (jobs : List Job) (t : Prosa_Behavior_Time_instant),
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
        @eq Bool
          (Bool_not
             (Bool_and (P j)
                (Prosa_Behavior_Service_scheduled_at Job
                   inst_3 PState sched
                   j t)))
          Bool_true) ->
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job
            inst_3 PState sched P jobs
            t)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
