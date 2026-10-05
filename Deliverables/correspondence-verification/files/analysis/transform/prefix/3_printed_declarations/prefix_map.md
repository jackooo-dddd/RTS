# `prefix_map`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.analysis.transform.prefix.prefix_map`
- Lean: `Prosa.Analysis.Transform.Prefix.prefix_map`
- Certificate: `prefix_map_correspondence`

## Official Rocq

```coq
prefix_map :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState ->
(@schedule Job PState -> instant -> @schedule Job PState) -> instant -> @schedule Job PState

prefix_map is not universe polymorphic
Arguments prefix_map {Job PState} sched f%function_scope horizon _
prefix_map is transparent
Expands to: Constant prosa.analysis.transform.prefix.prefix_map
Declared in library prosa.analysis.transform.prefix, line 21, characters 2-286
@prefix_map
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState ->
       (@schedule Job PState -> instant -> @schedule Job PState) -> instant -> @schedule Job PState
```

Body:

```coq
prefix_map =
fun (Job : JobType) (PState : ProcessorState Job) =>
fix prefix_map
  (sched : @schedule Job PState) (f : @schedule Job PState -> instant -> @schedule Job PState)
  (horizon : instant) {struct horizon} : @schedule Job PState :=
  match horizon with
  | 0 => sched
  | t.+1 => let prefix := prefix_map sched f t in f prefix t
  end
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState ->
       (@schedule Job PState -> instant -> @schedule Job PState) -> instant -> @schedule Job PState

Arguments prefix_map {Job PState} sched f%function_scope horizon _
```

## Lean

```lean
@Prosa.Analysis.Transform.Prefix.prefix_map : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        (Prosa.Behavior.Schedule.schedule PState →
            Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState) →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState
```

Body:

```lean
def Prosa.Analysis.Transform.Prefix.prefix_map.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        (Prosa.Behavior.Schedule.schedule PState →
            Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState) →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState :=
fun {Job} [DecidableEq Job] {PState} sched f x => Nat.brecOn x (Prosa.Analysis.Transform.Prefix.prefix_map._f sched f)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_Prefix_prefix_map
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Prosa_Behavior_Schedule_schedule Job
          inst_3 PState ->
        Prosa_Behavior_Time_instant ->
        Prosa_Behavior_Schedule_schedule Job
          inst_3 PState) ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState
```

Body:

```coq
Prosa_Analysis_Transform_Prefix_prefix_map@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (f : Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState)
  (x____at___Prosa_Analysis_Transform_Prefix989796092__hygCtx__hyg21 : Prosa_Behavior_Time_instant) =>
Nat_brecOn
  (fun _ : Prosa_Behavior_Time_instant =>
   Prosa_Behavior_Schedule_schedule Job inst_3
     PState)
  x____at___Prosa_Analysis_Transform_Prefix989796092__hygCtx__hyg21
  (Prosa_Analysis_Transform_Prefix_prefix_map__f Job
     inst_3 PState sched f)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Prosa_Behavior_Schedule_schedule Job
          inst_3 PState ->
        Prosa_Behavior_Time_instant ->
        Prosa_Behavior_Schedule_schedule Job
          inst_3 PState) ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState

Arguments Prosa_Analysis_Transform_Prefix_prefix_map Job
  inst_3 PState sched 
  f%_function_scope a____at____internal__hyg0 a____at____internal__hyg0
```
