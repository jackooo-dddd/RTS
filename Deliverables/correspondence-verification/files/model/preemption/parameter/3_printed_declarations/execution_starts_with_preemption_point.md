# `execution_starts_with_preemption_point`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.execution_starts_with_preemption_point`
- Lean: `Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point`
- Certificate: `execution_starts_with_preemption_point_correspondence`

## Official Rocq

```coq
execution_starts_with_preemption_point :
forall {Job : JobType},
JobPreemptable Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> Prop

execution_starts_with_preemption_point is not universe polymorphic
Arguments execution_starts_with_preemption_point {Job H1 PState} sched j
execution_starts_with_preemption_point is transparent
Expands to: Constant prosa.model.preemption.parameter.execution_starts_with_preemption_point
Declared in library prosa.model.preemption.parameter, line 119, characters 13-51
@execution_starts_with_preemption_point
     : forall Job : JobType,
       JobPreemptable Job ->
       forall PState : ProcessorState Job, @schedule Job PState -> Equality.sort Job -> Prop
```

Body:

```coq
execution_starts_with_preemption_point =
fun (Job : JobType) (H1 : JobPreemptable Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (j : Equality.sort Job) =>
forall prt : instant,
is_true (~~ @scheduled_at Job PState sched j prt) ->
is_true (@scheduled_at Job PState sched j prt.+1) ->
is_true (@job_preemptable Job H1 j (@service Job PState sched j prt.+1))
     : forall {Job : JobType},
       JobPreemptable Job ->
       forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> Prop

Arguments execution_starts_with_preemption_point {Job H1 PState} sched j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Job → Prop
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState} sched j =>
  ∀ (prt : Prosa.Behavior.Time.instant),
    (!Prosa.Behavior.Service.scheduled_at sched j prt) = true →
      Prosa.Behavior.Service.scheduled_at sched j (prt + 1) = true →
        Prosa.Model.Preemption.Parameter.job_preemptable j (Prosa.Behavior.Service.service sched j (prt + 1)) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_execution_starts_with_preemption_point
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
Prosa_Model_Preemption_Parameter_execution_starts_with_preemption_point@{u_1 u_2 u_3 Lean.u_1+1.0
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
forall prt : Prosa_Behavior_Time_instant,
@eq Bool
  (Bool_not
     (Prosa_Behavior_Service_scheduled_at Job
        inst_3 PState sched j prt))
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) prt
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
  Bool_true ->
@eq Bool
  (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
     inst_3
     inst_6 j
     (Prosa_Behavior_Service_service Job
        inst_3 PState sched j
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) prt
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
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

Arguments Prosa_Model_Preemption_Parameter_execution_starts_with_preemption_point 
  Job inst_3
  inst_6 PState sched
  a____at____internal__hyg0
```
