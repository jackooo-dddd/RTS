# `blackout_implies_no_service_inversion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.blackout_implies_no_service_inversion`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.blackout_implies_no_service_inversion`
- Certificate: `blackout_implies_no_service_inversion_correspondence`

## Official Rocq

```coq
blackout_implies_no_service_inversion :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {JLDP : JLDP_policy Job} (j : Equality.sort Job) 
  (t : instant),
is_true (@is_blackout Job PState sched t) ->
is_true (~~ @service_inversion Job PState arr_seq sched JLDP j t)

blackout_implies_no_service_inversion is not universe polymorphic
Arguments blackout_implies_no_service_inversion {Job PState} arr_seq sched {JLDP} j t _
blackout_implies_no_service_inversion is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.service_inversion.blackout_implies_no_service_inversion
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 44, characters 10-47
@blackout_implies_no_service_inversion
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLDP : JLDP_policy Job) (j : Equality.sort Job) 
         (t : instant),
       is_true (@is_blackout Job PState sched t) ->
       is_true (~~ @service_inversion Job PState arr_seq sched JLDP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.blackout_implies_no_service_inversion : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Supply.is_blackout sched t = true →
    (!Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_blackout_implies_no_service_inversion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState)
         (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
                   inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Supply_is_blackout Job
            inst_3 PState
            sched t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
               inst_3 PState
               arr_seq sched JLDP j t))
         Bool_true
```
