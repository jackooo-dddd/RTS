# `job_doesnt_complete_before_remaining_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.job_doesnt_complete_before_remaining_cost`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.job_doesnt_complete_before_remaining_cost`
- Certificate: `job_doesnt_complete_before_remaining_cost_correspondence`

## Official Rocq

```coq
job_doesnt_complete_before_remaining_cost :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState),
@completed_jobs_dont_execute Job PState sched H ->
forall j : Equality.sort Job,
@unit_service_proc_model Job PState ->
forall t : instant,
is_true (~~ @completed_by Job PState sched H j t) ->
is_true (~~ @completed_by Job PState sched H j (t + @remaining_cost Job PState sched H j t - 1))

job_doesnt_complete_before_remaining_cost is not universe polymorphic
Arguments job_doesnt_complete_before_remaining_cost {Job H PState} sched H_completed_jobs 
  j H_unit_service t _
job_doesnt_complete_before_remaining_cost is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.job_doesnt_complete_before_remaining_cost
Declared in library prosa.analysis.facts.behavior.completion, line 246, characters 8-49
@job_doesnt_complete_before_remaining_cost
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       @completed_jobs_dont_execute Job PState sched H ->
       forall j : Equality.sort Job,
       @unit_service_proc_model Job PState ->
       forall t : instant,
       is_true (~~ @completed_by Job PState sched H j t) ->
       is_true (~~ @completed_by Job PState sched H j (t + @remaining_cost Job PState sched H j t - 1))
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.job_doesnt_complete_before_remaining_cost : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (j : Job),
      Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
        ∀ (t : Prosa.Behavior.Time.instant),
          (!Prosa.Behavior.Service.completed_by sched j t) = true →
            (!Prosa.Behavior.Service.completed_by sched j (t + Prosa.Behavior.Service.remaining_cost sched j t - 1)) =
              true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_job_doesnt_complete_before_remaining_cost
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
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j t))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j
               (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Job_work
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                     (Prosa_Behavior_Service_remaining_cost Job
                        inst_3 PState
                        sched inst_6 j
                        t))
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
         Bool_true
```
