# `respects_JLDP_policy_at_preemption_point`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point`
- Lean: `Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point`
- Certificate: `respects_JLDP_policy_at_preemption_point_correspondence`

## Official Rocq

```coq
respects_JLDP_policy_at_preemption_point :
forall {Job : JobType} {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
JobPreemptable Job ->
@JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> JLDP_policy Job -> Prop

respects_JLDP_policy_at_preemption_point is not universe polymorphic
Arguments respects_JLDP_policy_at_preemption_point {Job H0 H1 PState H2 jr} arr_seq sched policy
respects_JLDP_policy_at_preemption_point is transparent
Expands to: Constant prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point
Declared in library prosa.model.schedule.priority_driven, line 48, characters 13-53
@respects_JLDP_policy_at_preemption_point
     : forall (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job),
       JobPreemptable Job ->
       @JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> JLDP_policy Job -> Prop
```

Body:

```coq
respects_JLDP_policy_at_preemption_point =
fun (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job)
  (H2 : JobPreemptable Job) (jr : @JobReady Job PState H1 H0) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (policy : JLDP_policy Job) =>
forall (j j_hp : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true (@preemption_time Job H2 arr_seq PState sched t) ->
is_true (@backlogged Job PState H1 H0 jr sched j t) ->
is_true (@scheduled_at Job PState sched j_hp t) -> is_true (@hep_job_at Job policy t j_hp j)
     : forall {Job : JobType} {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
       JobPreemptable Job ->
       @JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> JLDP_policy Job -> Prop

Arguments respects_JLDP_policy_at_preemption_point {Job H0 H1 PState H2 jr} arr_seq sched policy
```

## Lean

```lean
@Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
            [jr : Prosa.Behavior.Ready.JobReady Job PState] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop
```

Body:

```lean
def Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
            [jr : Prosa.Behavior.Ready.JobReady Job PState] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched
    policy =>
  ∀ (j j_hp : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t = true →
        Prosa.Behavior.Ready.backlogged sched j t = true →
          Prosa.Behavior.Service.scheduled_at sched j_hp t = true →
            Prosa.Model.Priority.Definitions.hep_job_at t j_hp j = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Prosa_Behavior_Ready_JobReady Job
         inst_7 PState
         inst_17
         inst_14 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_7 ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_14 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_7)
  (inst_17 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_7)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (inst_22 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                                Job
                                                                                inst_7)
  (jr : Prosa_Behavior_Ready_JobReady Job
          inst_7 PState
          inst_17
          inst_14)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (policy : Prosa_Model_Priority_Definitions_JLDP_policy Job
              inst_7) =>
forall (j j_hp : Job) (t : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_7 arr_seq j ->
@eq Bool
  (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
     inst_7
     inst_22 arr_seq PState sched t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Ready_backlogged Job
     inst_7 PState
     inst_17
     inst_14 jr sched j t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_7 PState sched j_hp t)
  Bool_true ->
@eq Bool
  (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
     inst_7 policy t j_hp j)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Prosa_Behavior_Ready_JobReady Job
         inst_7 PState
         inst_17
         inst_14 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_7 ->
       SProp

Arguments Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point 
  Job inst_7
  inst_14
  inst_17 PState
  inst_22 jr arr_seq 
  sched policy
```
