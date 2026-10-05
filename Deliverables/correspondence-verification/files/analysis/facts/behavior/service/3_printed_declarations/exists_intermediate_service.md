# `exists_intermediate_service`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.exists_intermediate_service`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service`
- Certificate: `exists_intermediate_service_correspondence`

## Official Rocq

```coq
exists_intermediate_service :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant) (s : duration),
is_true (s < @service Job PState sched j t) ->
exists t' : nat, is_true (t' < t) /\ @service Job PState sched j t' = s

exists_intermediate_service is not universe polymorphic
Arguments exists_intermediate_service {Job PState} H_unit_service sched j t s H_less_than_s
exists_intermediate_service is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.exists_intermediate_service
Declared in library prosa.analysis.facts.behavior.service, line 215, characters 14-41
@exists_intermediate_service
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant) (s : duration),
       is_true (s < @service Job PState sched j t) ->
       exists t' : nat, is_true (t' < t) /\ @service Job PState sched j t' = s
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
      ∀ s < Prosa.Behavior.Service.service sched j t, ∃ t' < t, Prosa.Behavior.Service.service sched j t' = s
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_exists_intermediate_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant) (s : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat s
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t) ->
       Exists Nat
         (fun t' : Nat =>
          And (LT_lt_inst1 Nat instLTNat t' t)
            (@eq Prosa_Behavior_Job_work
               (Prosa_Behavior_Service_service Job
                  inst_3 PState sched j
                  t')
               s))
```
