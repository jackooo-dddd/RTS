# `service_inversion_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.service_inversion_cat`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_cat`
- Certificate: `service_inversion_cat_correspondence`

## Official Rocq

```coq
service_inversion_cat :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {JLDP : JLDP_policy Job} (j : Equality.sort Job) 
  (t1 t2 t : instant),
is_true (t1 <= t) ->
is_true (t <= t2) ->
@cumulative_service_inversion Job PState arr_seq sched JLDP j t1 t2 =
@cumulative_service_inversion Job PState arr_seq sched JLDP j t1 t +
@cumulative_service_inversion Job PState arr_seq sched JLDP j t t2

service_inversion_cat is not universe polymorphic
Arguments service_inversion_cat {Job PState} arr_seq sched {JLDP} j t1 t2 t _ _
service_inversion_cat is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.service_inversion.service_inversion_cat
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 85, characters 10-31
@service_inversion_cat
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLDP : JLDP_policy Job) (j : Equality.sort Job) 
         (t1 t2 t : instant),
       is_true (t1 <= t) ->
       is_true (t <= t2) ->
       @cumulative_service_inversion Job PState arr_seq sched JLDP j t1 t2 =
       @cumulative_service_inversion Job PState arr_seq sched JLDP j t1 t +
       @cumulative_service_inversion Job PState arr_seq sched JLDP j t t2
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job) (j : Job) (t1 t2 t : Prosa.Behavior.Time.instant),
  t1 ≤ t →
    t ≤ t2 →
      Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j t1 t2 =
        Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j t1 t +
          Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inversion_cat
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
         (j : Job) (t1 t2 t : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t2 ->
       @eq Nat
         (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
            inst_3 PState
            arr_seq sched JLDP j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
               inst_3 PState
               arr_seq sched JLDP j t1 t)
            (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
               inst_3 PState
               arr_seq sched JLDP j t t2))
```
