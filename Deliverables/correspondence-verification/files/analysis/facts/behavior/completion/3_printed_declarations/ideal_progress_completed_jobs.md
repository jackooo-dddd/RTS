# `ideal_progress_completed_jobs`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.ideal_progress_completed_jobs`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.ideal_progress_completed_jobs`
- Certificate: `ideal_progress_completed_jobs_correspondence`

## Official Rocq

```coq
ideal_progress_completed_jobs :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) {H : JobCost Job},
@ideal_progress_proc_model Job PState ->
(forall (j : Equality.sort Job) (t : instant), is_true (@service Job PState sched j t <= @job_cost Job H j)) ->
@completed_jobs_dont_execute Job PState sched H

ideal_progress_completed_jobs is not universe polymorphic
Arguments ideal_progress_completed_jobs {Job PState} sched {H} _ _%function_scope j t _
ideal_progress_completed_jobs is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.ideal_progress_completed_jobs
Declared in library prosa.analysis.facts.behavior.completion, line 379, characters 8-37
@ideal_progress_completed_jobs
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (H : JobCost Job),
       @ideal_progress_proc_model Job PState ->
       (forall (j : Equality.sort Job) (t : instant),
        is_true (@service Job PState sched j t <= @job_cost Job H j)) ->
       @completed_jobs_dont_execute Job PState sched H
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.ideal_progress_completed_jobs : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job],
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    (∀ (j : Job) (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.service sched j t ≤ Prosa.Behavior.Job.job_cost j) →
      Prosa.Behavior.Ready.completed_jobs_dont_execute sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_ideal_progress_completed_jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_10 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       (forall (j : Job) (t : Prosa_Behavior_Time_instant),
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Service_service Job
             inst_3 PState sched j t)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             inst_10 j)) ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_10
```
