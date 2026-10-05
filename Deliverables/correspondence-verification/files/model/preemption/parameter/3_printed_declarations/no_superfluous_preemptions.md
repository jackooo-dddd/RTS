# `no_superfluous_preemptions`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.no_superfluous_preemptions`
- Lean: `Prosa.Model.Preemption.Parameter.no_superfluous_preemptions`
- Certificate: `no_superfluous_preemptions_correspondence`

## Official Rocq

```coq
no_superfluous_preemptions :
forall {Job : JobType},
JobCost Job -> JLDP_policy Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

no_superfluous_preemptions is not universe polymorphic
Arguments no_superfluous_preemptions {Job H0 H2 PState} sched
no_superfluous_preemptions is transparent
Expands to: Constant prosa.model.preemption.parameter.no_superfluous_preemptions
Declared in library prosa.model.preemption.parameter, line 137, characters 13-39
@no_superfluous_preemptions
     : forall Job : JobType,
       JobCost Job -> JLDP_policy Job -> forall PState : ProcessorState Job, @schedule Job PState -> Prop
```

Body:

```coq
no_superfluous_preemptions =
fun (Job : JobType) (H0 : JobCost Job) (H2 : JLDP_policy Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) =>
forall (t : instant) (j j_hp : Equality.sort Job),
is_true (@preempted_at Job H0 PState sched j t) ->
is_true (@scheduled_at Job PState sched j_hp t) -> is_true (~~ @hep_job_at Job H2 t j j_hp)
     : forall {Job : JobType},
       JobCost Job -> JLDP_policy Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

Arguments no_superfluous_preemptions {Job H0 H2 PState} sched
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.no_superfluous_preemptions : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.no_superfluous_preemptions.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Priority.Definitions.JLDP_policy Job] {PState}
    sched =>
  ∀ (t : Prosa.Behavior.Time.instant) (j j_hp : Job),
    Prosa.Model.Preemption.Parameter.preempted_at sched j t = true →
      Prosa.Behavior.Service.scheduled_at sched j_hp t = true →
        (!Prosa.Model.Priority.Definitions.hep_job_at t j j_hp) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_no_superfluous_preemptions
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Model_Preemption_Parameter_no_superfluous_preemptions@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (inst_9 : Prosa_Model_Priority_Definitions_JLDP_policy
                                                                             Job
                                                                             inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (t : Prosa_Behavior_Time_instant) (j j_hp : Job),
@eq Bool
  (Prosa_Model_Preemption_Parameter_preempted_at Job
     inst_3
     inst_6 PState sched j t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j_hp t)
  Bool_true ->
@eq Bool
  (Bool_not
     (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
        inst_3
        inst_9 t j j_hp))
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Model_Preemption_Parameter_no_superfluous_preemptions Job
  inst_3
  inst_6
  inst_9 PState sched
```
