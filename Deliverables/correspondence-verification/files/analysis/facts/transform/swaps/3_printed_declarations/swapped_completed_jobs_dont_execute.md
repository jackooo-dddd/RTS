# `swapped_completed_jobs_dont_execute`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swapped_completed_jobs_dont_execute`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swapped_completed_jobs_dont_execute`
- Certificate: `swapped_completed_jobs_dont_execute_correspondence`

## Official Rocq

```coq
swapped_completed_jobs_dont_execute :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (t1 t2 : instant),
is_true (t1 <= t2) ->
@unit_service_proc_model Job PState ->
@ideal_progress_proc_model Job PState ->
@completed_jobs_dont_execute Job PState sched H ->
@completed_jobs_dont_execute Job PState (@swapped Job PState sched t1 t2) H

swapped_completed_jobs_dont_execute is not universe polymorphic
Arguments swapped_completed_jobs_dont_execute {Job H PState} sched t1 t2 H_order _ _ _ j t _
swapped_completed_jobs_dont_execute is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swapped_completed_jobs_dont_execute
Declared in library prosa.analysis.facts.transform.swaps, line 319, characters 8-43
@swapped_completed_jobs_dont_execute
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (t1 t2 : instant),
       is_true (t1 <= t2) ->
       @unit_service_proc_model Job PState ->
       @ideal_progress_proc_model Job PState ->
       @completed_jobs_dont_execute Job PState sched H ->
       @completed_jobs_dont_execute Job PState (@swapped Job PState sched t1 t2) H
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swapped_completed_jobs_dont_execute : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  [inst_1 : Prosa.Behavior.Job.JobCost Job] (sched : Prosa.Behavior.Schedule.schedule PState)
  (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
        Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute (Prosa.Analysis.Transform.Swap.swapped sched t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swapped_completed_jobs_dont_execute
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_8 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_8 ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState
         (Prosa_Analysis_Transform_Swap_swapped Job
            inst_3 PState sched t1 t2)
         inst_8
```
