# `service_of_jobs_le_workload`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_workload`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_le_workload`
- Certificate: `service_of_jobs_le_workload_correspondence`

## Official Rocq

```coq
service_of_jobs_le_workload :
forall {Job : JobType} {H1 : JobCost Job} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall sched : @schedule Job PState,
@completed_jobs_dont_execute Job PState sched H1 ->
forall (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
is_true (@service_of_jobs Job PState sched P jobs t1 t2 <= @workload_of_jobs Job H1 P jobs)

service_of_jobs_le_workload is not universe polymorphic
Arguments service_of_jobs_le_workload {Job H1 PState} H_unit_service_proc_model sched
  H_completed_jobs_dont_execute P jobs%seq_scope t1 t2
service_of_jobs_le_workload is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_workload
Declared in library prosa.analysis.facts.model.service_of_jobs, line 325, characters 8-35
@service_of_jobs_le_workload
     : forall (Job : JobType) (H1 : JobCost Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall sched : @schedule Job PState,
       @completed_jobs_dont_execute Job PState sched H1 ->
       forall (P : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)) (t1 t2 : instant),
       is_true (@service_of_jobs Job PState sched P jobs t1 t2 <= @workload_of_jobs Job H1 P jobs)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_le_workload : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
        ∀ (P : Job → Bool) (jobs : List Job) (t1 t2 : Prosa.Behavior.Time.instant),
          Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P jobs t1 t2 ≤
            Prosa.Model.Aggregate.Workload.workload_of_jobs P jobs
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_le_workload
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_6 ->
       forall (P : Job -> Bool) (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P jobs
            t1 t2)
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P jobs)
```
