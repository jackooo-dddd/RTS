# `respects_JLFP_policy_at_preemption_point`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point`
- Lean: `Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point`
- Certificate: `respects_JLFP_policy_at_preemption_point_correspondence`

## Official Rocq

```coq
respects_JLFP_policy_at_preemption_point :
forall {Job : JobType} {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
JobPreemptable Job ->
@JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Prop

respects_JLFP_policy_at_preemption_point is not universe polymorphic
Arguments respects_JLFP_policy_at_preemption_point {Job H0 H1 PState H2 jr} arr_seq sched policy
respects_JLFP_policy_at_preemption_point is transparent
Expands to: Constant prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point
Declared in library prosa.model.schedule.priority_driven, line 57, characters 13-53
@respects_JLFP_policy_at_preemption_point
     : forall (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job),
       JobPreemptable Job ->
       @JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Prop
```

Body:

```coq
respects_JLFP_policy_at_preemption_point =
fun (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job)
  (H2 : JobPreemptable Job) (jr : @JobReady Job PState H1 H0) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (policy : JLFP_policy Job) =>
@respects_JLDP_policy_at_preemption_point Job H0 H1 PState H2 jr arr_seq sched (@JLFP_to_JLDP Job policy)
     : forall {Job : JobType} {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
       JobPreemptable Job ->
       @JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Prop

Arguments respects_JLFP_policy_at_preemption_point {Job H0 H1 PState H2 jr} arr_seq sched policy
```

## Lean

```lean
@Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
            [jr : Prosa.Behavior.Ready.JobReady Job PState] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop
```

Body:

```lean
def Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
            [jr : Prosa.Behavior.Ready.JobReady Job PState] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched
    policy =>
  Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point arr_seq sched
    Prosa.Model.Priority.Coercion.JLFP_to_JLDP
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
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
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point@{u_1 u_2 u_3 Lean.u_1+1.0
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
  (policy : Prosa_Model_Priority_Definitions_JLFP_policy Job
              inst_7) =>
Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point Job
  inst_7
  inst_14
  inst_17 PState
  inst_22 jr arr_seq sched
  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
     inst_7 policy)
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
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       SProp

Arguments Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point 
  Job inst_7
  inst_14
  inst_17 PState
  inst_22 jr arr_seq 
  sched policy
```
