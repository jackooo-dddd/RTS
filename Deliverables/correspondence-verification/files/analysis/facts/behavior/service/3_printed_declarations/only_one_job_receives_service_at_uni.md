# `only_one_job_receives_service_at_uni`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.only_one_job_receives_service_at_uni`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.only_one_job_receives_service_at_uni`
- Certificate: `only_one_job_receives_service_at_uni_correspondence`

## Official Rocq

```coq
only_one_job_receives_service_at_uni :
forall {Job : JobType} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) (j1 j2 : Equality.sort Job) (t : instant),
is_true (@receives_service_at Job PState sched j1 t) ->
is_true (@receives_service_at Job PState sched j2 t) -> j1 = j2

only_one_job_receives_service_at_uni is not universe polymorphic
Arguments only_one_job_receives_service_at_uni {Job PState} H_uniprocessor_proc_model sched j1 j2 t _ _
only_one_job_receives_service_at_uni is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.only_one_job_receives_service_at_uni
Declared in library prosa.analysis.facts.behavior.service, line 750, characters 8-44
@only_one_job_receives_service_at_uni
     : forall (Job : JobType) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (j1 j2 : Equality.sort Job) (t : instant),
       is_true (@receives_service_at Job PState sched j1 t) ->
       is_true (@receives_service_at Job PState sched j2 t) -> j1 = j2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.only_one_job_receives_service_at_uni : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j1 j2 : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.receives_service_at sched j1 t = true →
        Prosa.Behavior.Service.receives_service_at sched j2 t = true → j1 = j2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_only_one_job_receives_service_at_uni
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j1 j2 : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_3 PState sched j1 t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_3 PState sched j2 t)
         Bool_true ->
       @eq Job j1 j2
```
