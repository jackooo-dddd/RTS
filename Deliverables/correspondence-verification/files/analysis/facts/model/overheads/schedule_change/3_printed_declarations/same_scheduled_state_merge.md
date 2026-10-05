# `same_scheduled_state_merge`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change.same_scheduled_state_merge`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.same_scheduled_state_merge`
- Certificate: `same_scheduled_state_merge_correspondence`

## Official Rocq

```coq
same_scheduled_state_merge :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t1 t2 t : instant)
  (oj1 oj2 : option (Equality.sort Job)),
is_true (t1 < t < t2) ->
is_true (~~ @schedule_change Job sched t) ->
is_true (@scheduled_job_invariant Job sched oj1 t1 t) ->
is_true (@scheduled_job_invariant Job sched oj2 t t2) -> oj1 = oj2

same_scheduled_state_merge is not universe polymorphic
Arguments same_scheduled_state_merge {Job} sched t1 t2 t oj1 oj2 _ _ _ _
same_scheduled_state_merge is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule_change.same_scheduled_state_merge
Declared in library prosa.analysis.facts.model.overheads.schedule_change, line 103, characters 8-34
@same_scheduled_state_merge
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 t : instant)
         (oj1 oj2 : option (Equality.sort Job)),
       is_true (t1 < t < t2) ->
       is_true (~~ @schedule_change Job sched t) ->
       is_true (@scheduled_job_invariant Job sched oj1 t1 t) ->
       is_true (@scheduled_job_invariant Job sched oj2 t t2) -> oj1 = oj2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.same_scheduled_state_merge : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t1 t2 t : Prosa.Behavior.Time.instant) (oj1 oj2 : Option Job),
  (decide (t1 < t) && decide (t < t2)) = true →
    (!Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change sched t) = true →
      Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant sched oj1 t1 t = true →
        Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant sched oj2 t t2 = true → oj1 = oj2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_same_scheduled_state_merge
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t1 t2 t : Prosa_Behavior_Time_instant) (oj1 oj2 : Option Job),
       @eq Bool
         (Bool_and
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change Job
               inst_3 sched
               t))
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant Job
            inst_3 sched
            oj1 t1 t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant Job
            inst_3 sched
            oj2 t t2)
         Bool_true ->
       @eq (Option Job) oj1 oj2
```
