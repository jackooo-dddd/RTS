# `service_of_jobs_le_length_of_interval`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_le_length_of_interval`
- Certificate: `service_of_jobs_le_length_of_interval_correspondence`

## Official Rocq

```coq
service_of_jobs_le_length_of_interval :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)),
is_true (@uniq Job jobs) ->
forall (t : instant) (Δ : duration), is_true (@service_of_jobs Job PState sched P jobs t (t + Δ) <= Δ)

service_of_jobs_le_length_of_interval is not universe polymorphic
Arguments service_of_jobs_le_length_of_interval {Job PState} H_unit_service_proc_model 
  H_uniprocessor_model sched P jobs%seq_scope H_no_duplicate_jobs t Δ
service_of_jobs_le_length_of_interval is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval
Declared in library prosa.analysis.facts.model.service_of_jobs, line 500, characters 14-51
@service_of_jobs_le_length_of_interval
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)),
       is_true (@uniq Job jobs) ->
       forall (t : instant) (Δ : duration), is_true (@service_of_jobs Job PState sched P jobs t (t + Δ) <= Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_le_length_of_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
      ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (jobs : List Job),
        jobs.Nodup →
          ∀ (t : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration),
            Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P jobs t (t + Δ) ≤ Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_le_length_of_interval
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
       forall (t : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P jobs
            t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU0394_))
         _UU0394_
```
