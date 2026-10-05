# `prefix_map_property_invariance`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.transform.prefix.prefix_map_property_invariance`
- Lean: `Prosa.Analysis.Transform.Prefix.prefix_map_property_invariance`
- Certificate: `prefix_map_property_invariance_correspondence`

## Official Rocq

```coq
prefix_map_property_invariance :
forall {Job : JobType} {PState : ProcessorState Job} (P : @schedule Job PState -> Prop)
  (f : @schedule Job PState -> instant -> @schedule Job PState),
(forall (sched : @schedule Job PState) (t : instant), P sched -> P (f sched t)) ->
forall (sched : @schedule Job PState) (h : instant), P sched -> P (@prefix_map Job PState sched f h)

prefix_map_property_invariance is not universe polymorphic
Arguments prefix_map_property_invariance {Job PState} (P f H_f_maintains_P)%function_scope sched h _
prefix_map_property_invariance is opaque
Expands to: Constant prosa.analysis.transform.prefix.prefix_map_property_invariance
Declared in library prosa.analysis.transform.prefix, line 49, characters 10-40
@prefix_map_property_invariance
     : forall (Job : JobType) (PState : ProcessorState Job) (P : @schedule Job PState -> Prop)
         (f : @schedule Job PState -> instant -> @schedule Job PState),
       (forall (sched : @schedule Job PState) (t : instant), P sched -> P (f sched t)) ->
       forall (sched : @schedule Job PState) (h : instant), P sched -> P (@prefix_map Job PState sched f h)
```

## Lean

```lean
@Prosa.Analysis.Transform.Prefix.prefix_map_property_invariance : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (P : Prosa.Behavior.Schedule.schedule PState → Prop)
  (f : Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState),
  (∀ (sched : Prosa.Behavior.Schedule.schedule PState) (t : Prosa.Behavior.Time.instant), P sched → P (f sched t)) →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (h : Prosa.Behavior.Time.instant),
      P sched → P (Prosa.Analysis.Transform.Prefix.prefix_map sched f h)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_Prefix_prefix_map_property_invariance
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (P : Prosa_Behavior_Schedule_schedule Job
                inst_3 PState ->
              SProp)
         (f : Prosa_Behavior_Schedule_schedule Job
                inst_3 PState ->
              Prosa_Behavior_Time_instant ->
              Prosa_Behavior_Schedule_schedule Job
                inst_3 PState),
       (forall
          (sched : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
          (t : Prosa_Behavior_Time_instant),
        P sched -> P (f sched t)) ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (h : Prosa_Behavior_Time_instant),
       P sched ->
       P
         (Prosa_Analysis_Transform_Prefix_prefix_map Job
            inst_3 PState sched f h)
```
