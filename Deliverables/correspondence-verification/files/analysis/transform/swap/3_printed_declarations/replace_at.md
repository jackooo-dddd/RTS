# `replace_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.swap.replace_at`
- Lean: `Prosa.Analysis.Transform.Swap.replace_at`
- Certificate: `replace_at_correspondence`

## Official Rocq

```coq
replace_at :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> instant -> @State Job PState -> @schedule Job PState

replace_at is not universe polymorphic
Arguments replace_at {Job PState} original_sched t' new_state _
replace_at is transparent
Expands to: Constant prosa.analysis.transform.swap.replace_at
Declared in library prosa.analysis.transform.swap, line 25, characters 13-23
@replace_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> instant -> @State Job PState -> @schedule Job PState
```

Body:

```coq
replace_at =
fun (Job : JobType) (PState : ProcessorState Job) (original_sched : @schedule Job PState) 
  (t' : instant) (new_state : @State Job PState) (t : instant) =>
if t' == t then new_state else original_sched t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> instant -> @State Job PState -> @schedule Job PState

Arguments replace_at {Job PState} original_sched t' new_state _
```

## Lean

```lean
@Prosa.Analysis.Transform.Swap.replace_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Prosa.Behavior.Time.instant →
          Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Schedule.schedule PState
def Prosa.Analysis.Transform.Swap.replace_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Prosa.Behavior.Time.instant →
          Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Schedule.schedule PState :=
fun {Job} [DecidableEq Job] {PState} original_sched t' new_state t =>
  if (t' == t) = true then new_state else original_sched t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_Swap_replace_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState
```

Body:

```coq
Prosa_Analysis_Transform_Swap_replace_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0
Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (original_sched : Prosa_Behavior_Schedule_schedule Job
                      inst_3 PState)
  (t' : Prosa_Behavior_Time_instant)
  (new_state : Prosa_Behavior_Schedule_ProcessorState_State Job
                 inst_3 PState)
  (t : Prosa_Behavior_Time_instant) =>
ite
  (Prosa_Behavior_Schedule_ProcessorState_State Job
     inst_3 PState)
  (@eq Bool
     (BEq_beq_inst1 Prosa_Behavior_Time_instant
        (instBEqOfDecidableEq_inst1 Prosa_Behavior_Time_instant instDecidableEqNat) t' t)
     Bool_true)
  (instDecidableEqBool
     (BEq_beq_inst1 Prosa_Behavior_Time_instant
        (instBEqOfDecidableEq_inst1 Prosa_Behavior_Time_instant instDecidableEqNat) t' t)
     Bool_true)
  new_state (original_sched t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_schedule Job inst_3
         PState

Arguments Prosa_Analysis_Transform_Swap_replace_at Job
  inst_3 PState original_sched 
  t' new_state a____at____internal__hyg0
```
