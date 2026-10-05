# `service_of_jobs_le_1`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_1`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_le_1`
- Certificate: `service_of_jobs_le_1_correspondence`

## Official Rocq

```coq
service_of_jobs_le_1 :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)),
is_true (@uniq Job jobs) -> forall t : instant, is_true (@service_of_jobs_at Job PState sched P jobs t <= 1)

service_of_jobs_le_1 is not universe polymorphic
Arguments service_of_jobs_le_1 {Job PState} H_unit_service_proc_model H_uniprocessor_model 
  sched P jobs%seq_scope H_no_duplicate_jobs t
service_of_jobs_le_1 is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_1
Declared in library prosa.analysis.facts.model.service_of_jobs, line 474, characters 10-30
@service_of_jobs_le_1
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)),
       is_true (@uniq Job jobs) ->
       forall t : instant, is_true (@service_of_jobs_at Job PState sched P jobs t <= 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_le_1 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
      ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (jobs : List Job),
        jobs.Nodup →
          ∀ (t : Prosa.Behavior.Time.instant), Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at sched P jobs t ≤ 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_le_1
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool) (jobs : List Job),
       List_Nodup Job jobs ->
       forall t : Prosa_Behavior_Time_instant,
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job
            inst_3 PState sched P jobs
            t)
         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
```
