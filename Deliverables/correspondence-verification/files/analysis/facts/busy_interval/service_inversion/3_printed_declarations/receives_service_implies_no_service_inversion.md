# `receives_service_implies_no_service_inversion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.receives_service_implies_no_service_inversion`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.receives_service_implies_no_service_inversion`
- Certificate: `receives_service_implies_no_service_inversion_correspondence`

## Official Rocq

```coq
receives_service_implies_no_service_inversion :
forall {Job : JobType} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {JLDP : JLDP_policy Job},
@reflexive_priorities Job JLDP ->
forall (j : Equality.sort Job) (t : instant),
is_true (@receives_service_at Job PState sched j t) ->
is_true (~~ @service_inversion Job PState arr_seq sched JLDP j t)

receives_service_implies_no_service_inversion is not universe polymorphic
Arguments receives_service_implies_no_service_inversion {Job PState} H_uniprocessor_proc_model 
  arr_seq sched {JLDP} H_priority_is_reflexive j t _
receives_service_implies_no_service_inversion is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.service_inversion.receives_service_implies_no_service_inversion
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 71, characters 10-55
@receives_service_implies_no_service_inversion
     : forall (Job : JobType) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (JLDP : JLDP_policy Job),
       @reflexive_priorities Job JLDP ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@receives_service_at Job PState sched j t) ->
       is_true (~~ @service_inversion Job PState arr_seq sched JLDP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.receives_service_implies_no_service_inversion : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job),
      Prosa.Model.Priority.Definitions.reflexive_priorities JLDP →
        ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Service.receives_service_at sched j t = true →
            (!Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_receives_service_implies_no_service_inversion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState)
         (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_reflexive_priorities Job
         inst_3 JLDP ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_3 PState
            sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
               inst_3 PState
               arr_seq sched JLDP j t))
         Bool_true
```
