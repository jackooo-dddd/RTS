# `not_preemptive_implies_scheduled`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.not_preemptive_implies_scheduled`
- Lean: `Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled`
- Certificate: `not_preemptive_implies_scheduled_correspondence`

## Official Rocq

```coq
not_preemptive_implies_scheduled :
forall {Job : JobType},
JobPreemptable Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> Prop

not_preemptive_implies_scheduled is not universe polymorphic
Arguments not_preemptive_implies_scheduled {Job H1 PState} sched j
not_preemptive_implies_scheduled is transparent
Expands to: Constant prosa.model.preemption.parameter.not_preemptive_implies_scheduled
Declared in library prosa.model.preemption.parameter, line 113, characters 13-45
@not_preemptive_implies_scheduled
     : forall Job : JobType,
       JobPreemptable Job ->
       forall PState : ProcessorState Job, @schedule Job PState -> Equality.sort Job -> Prop
```

Body:

```coq
not_preemptive_implies_scheduled =
fun (Job : JobType) (H1 : JobPreemptable Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (j : Equality.sort Job) =>
forall t : instant,
is_true (~~ @job_preemptable Job H1 j (@service Job PState sched j t)) ->
is_true (@scheduled_at Job PState sched j t)
     : forall {Job : JobType},
       JobPreemptable Job ->
       forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> Prop

Arguments not_preemptive_implies_scheduled {Job H1 PState} sched j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Job → Prop
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState} sched j =>
  ∀ (t : Prosa.Behavior.Time.instant),
    (!Prosa.Model.Preemption.Parameter.job_preemptable j (Prosa.Behavior.Service.service sched j t)) = true →
      Prosa.Behavior.Service.scheduled_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_not_preemptive_implies_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> SProp
```

Body:

```coq
Prosa_Model_Preemption_Parameter_not_preemptive_implies_scheduled@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                             Job
                                                                             inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) =>
forall t : Prosa_Behavior_Time_instant,
@eq Bool
  (Bool_not
     (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
        inst_3
        inst_6 j
        (Prosa_Behavior_Service_service Job
           inst_3 PState sched j t)))
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> SProp

Arguments Prosa_Model_Preemption_Parameter_not_preemptive_implies_scheduled Job
  inst_3
  inst_6 PState sched
  a____at____internal__hyg0
```
