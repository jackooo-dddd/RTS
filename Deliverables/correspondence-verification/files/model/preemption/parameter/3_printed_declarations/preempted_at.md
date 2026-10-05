# `preempted_at`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.preempted_at`
- Lean: `Prosa.Model.Preemption.Parameter.preempted_at`
- Certificate: `preempted_at_correspondence`

## Official Rocq

```coq
preempted_at :
forall {Job : JobType},
JobCost Job ->
forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> instant -> bool

preempted_at is not universe polymorphic
Arguments preempted_at {Job H0 PState} sched j t
preempted_at is transparent
Expands to: Constant prosa.model.preemption.parameter.preempted_at
Declared in library prosa.model.preemption.parameter, line 95, characters 13-25
@preempted_at
     : forall Job : JobType,
       JobCost Job ->
       forall PState : ProcessorState Job, @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
preempted_at =
fun (Job : JobType) (H0 : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (j : Equality.sort Job) (t : instant) =>
@scheduled_at Job PState sched j t.-1 && ~~ @completed_by Job PState sched H0 j t &&
~~ @scheduled_at Job PState sched j t
     : forall {Job : JobType},
       JobCost Job ->
       forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments preempted_at {Job H0 PState} sched j t
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.preempted_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.preempted_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] {PState} sched j t =>
  Prosa.Behavior.Service.scheduled_at sched j (t - 1) && !Prosa.Behavior.Service.completed_by sched j t &&
    !Prosa.Behavior.Service.scheduled_at sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_preempted_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Preemption_Parameter_preempted_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_and
  (Bool_and
     (Prosa_Behavior_Service_scheduled_at Job
        inst_3 PState sched j
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
     (Bool_not
        (Prosa_Behavior_Service_completed_by Job
           inst_3 PState sched
           inst_6 j t)))
  (Bool_not
     (Prosa_Behavior_Service_scheduled_at Job
        inst_3 PState sched j t))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Preemption_Parameter_preempted_at Job
  inst_3
  inst_6 PState sched 
  j t
```
