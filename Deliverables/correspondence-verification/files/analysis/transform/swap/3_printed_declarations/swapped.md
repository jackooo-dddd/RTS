# `swapped`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.swap.swapped`
- Lean: `Prosa.Analysis.Transform.Swap.swapped`
- Certificate: `swapped_correspondence`

## Official Rocq

```coq
swapped :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> instant -> instant -> @schedule Job PState

swapped is not universe polymorphic
Arguments swapped {Job PState} original_sched t1 t2 _
swapped is transparent
Expands to: Constant prosa.analysis.transform.swap.swapped
Declared in library prosa.analysis.transform.swap, line 46, characters 13-20
@swapped
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> instant -> instant -> @schedule Job PState
```

Body:

```coq
swapped =
fun (Job : JobType) (PState : ProcessorState Job) (original_sched : @schedule Job PState) (t1 t2 : instant) =>
let s1 := original_sched t1 in
let s2 := original_sched t2 in
let replaced_s1 := @replace_at Job PState original_sched t1 s2 in @replace_at Job PState replaced_s1 t2 s1
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> instant -> instant -> @schedule Job PState

Arguments swapped {Job PState} original_sched t1 t2 _
```

## Lean

```lean
@Prosa.Analysis.Transform.Swap.swapped : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState
def Prosa.Analysis.Transform.Swap.swapped.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState :=
fun {Job} [DecidableEq Job] {PState} original_sched t1 t2 =>
  have s1 := original_sched t1;
  have s2 := original_sched t2;
  have replaced_s1 := Prosa.Analysis.Transform.Swap.replace_at original_sched t1 s2;
  Prosa.Analysis.Transform.Swap.replace_at replaced_s1 t2 s1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_Swap_swapped
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState
```

Body:

```coq
Prosa_Analysis_Transform_Swap_swapped@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0
Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (original_sched : Prosa_Behavior_Schedule_schedule Job
                      inst_3 PState)
  (t1 t2 : Prosa_Behavior_Time_instant) =>
let s1 := original_sched t1 in
let s2 := original_sched t2 in
let replaced_s1 :=
  Prosa_Analysis_Transform_Swap_replace_at Job
    inst_3 PState original_sched t1 s2
  in
Prosa_Analysis_Transform_Swap_replace_at Job
  inst_3 PState replaced_s1 t2 s1
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState

Arguments Prosa_Analysis_Transform_Swap_swapped Job
  inst_3 PState original_sched 
  t1 t2 a____at____internal__hyg0
```
