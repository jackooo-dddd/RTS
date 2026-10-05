# `cumulative_service_le_job_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.cumulative_service_le_job_cost`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.cumulative_service_le_job_cost`
- Certificate: `cumulative_service_le_job_cost_correspondence`

## Official Rocq

```coq
cumulative_service_le_job_cost :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState),
@completed_jobs_dont_execute Job PState sched H ->
forall j : Equality.sort Job,
@unit_service_proc_model Job PState ->
forall t t' : instant, is_true (@service_during Job PState sched j t t' <= @job_cost Job H j)

cumulative_service_le_job_cost is not universe polymorphic
Arguments cumulative_service_le_job_cost {Job H PState} sched H_completed_jobs j H_unit_service t t'
cumulative_service_le_job_cost is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.cumulative_service_le_job_cost
Declared in library prosa.analysis.facts.behavior.completion, line 234, characters 8-38
@cumulative_service_le_job_cost
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       @completed_jobs_dont_execute Job PState sched H ->
       forall j : Equality.sort Job,
       @unit_service_proc_model Job PState ->
       forall t t' : instant, is_true (@service_during Job PState sched j t t' <= @job_cost Job H j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.cumulative_service_le_job_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (j : Job),
      Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
        ∀ (t t' : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Service.service_during sched j t t' ≤ Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_cumulative_service_le_job_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_6 ->
       forall j : Job,
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall t t' : Prosa_Behavior_Time_instant,
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t t')
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j)
```
