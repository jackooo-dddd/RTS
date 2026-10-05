# `idle_time_is_pt`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.preemption.idle_time_is_pt`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.idle_time_is_pt`
- Certificate: `idle_time_is_pt_correspondence`

## Official Rocq

```coq
idle_time_is_pt :
forall {Job : JobType} {H1 : JobPreemptable Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState) (t : instant),
is_true (@is_idle Job PState arr_seq sched t) -> is_true (@preemption_time Job H1 arr_seq PState sched t)

idle_time_is_pt is not universe polymorphic
Arguments idle_time_is_pt {Job H1} arr_seq {PState} sched t _
idle_time_is_pt is opaque
Expands to: Constant prosa.analysis.facts.model.preemption.idle_time_is_pt
Declared in library prosa.analysis.facts.model.preemption, line 50, characters 8-23
@idle_time_is_pt
     : forall (Job : JobType) (H1 : JobPreemptable Job) (arr_seq : arrival_sequence Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (t : instant),
       is_true (@is_idle Job PState arr_seq sched t) ->
       is_true (@preemption_time Job H1 arr_seq PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.idle_time_is_pt : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
    Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_idle_time_is_pt
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq sched t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
            inst_3
            inst_6 arr_seq PState sched t)
         Bool_true
```
