# `service_inversion_widen`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.service_inversion_widen`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_widen`
- Certificate: `service_inversion_widen_correspondence`

## Official Rocq

```coq
service_inversion_widen :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {JLDP : JLDP_policy Job} (j : Equality.sort Job) 
  (al ar bl br : instant),
is_true (bl <= al) ->
is_true (ar <= br) ->
is_true
  (@cumulative_service_inversion Job PState arr_seq sched JLDP j al ar <=
   @cumulative_service_inversion Job PState arr_seq sched JLDP j bl br)

service_inversion_widen is not universe polymorphic
Arguments service_inversion_widen {Job PState} arr_seq sched {JLDP} j al ar bl br _ _
service_inversion_widen is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.service_inversion.service_inversion_widen
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 97, characters 10-33
@service_inversion_widen
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLDP : JLDP_policy Job) (j : Equality.sort Job)
         (al ar bl br : instant),
       is_true (bl <= al) ->
       is_true (ar <= br) ->
       is_true
         (@cumulative_service_inversion Job PState arr_seq sched JLDP j al ar <=
          @cumulative_service_inversion Job PState arr_seq sched JLDP j bl br)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_widen : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job) (j : Job) (al ar bl br : Prosa.Behavior.Time.instant),
  bl ≤ al →
    ar ≤ br →
      Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j al ar ≤
        Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j bl br
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inversion_widen
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
         (j : Job) (al ar bl br : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat bl al ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat ar br ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
            inst_3 PState
            arr_seq sched JLDP j al ar)
         (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
            inst_3 PState
            arr_seq sched JLDP j bl br)
```
