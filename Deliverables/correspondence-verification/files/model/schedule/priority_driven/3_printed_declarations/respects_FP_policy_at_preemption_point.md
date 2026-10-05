# `respects_FP_policy_at_preemption_point`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point`
- Lean: `Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point`
- Certificate: `respects_FP_policy_at_preemption_point_correspondence`

## Official Rocq

```coq
respects_FP_policy_at_preemption_point :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
forall {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
JobPreemptable Job ->
@JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> FP_policy Task -> Prop

respects_FP_policy_at_preemption_point is not universe polymorphic
Arguments respects_FP_policy_at_preemption_point {Task Job H H0 H1 PState H2 jr} arr_seq sched policy
respects_FP_policy_at_preemption_point is transparent
Expands to: Constant prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point
Declared in library prosa.model.schedule.priority_driven, line 61, characters 13-51
@respects_FP_policy_at_preemption_point
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       forall (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job),
       JobPreemptable Job ->
       @JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> FP_policy Task -> Prop
```

Body:

```coq
respects_FP_policy_at_preemption_point =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (PState : ProcessorState Job) (H2 : JobPreemptable Job)
  (jr : @JobReady Job PState H1 H0) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (policy : FP_policy Task) =>
@respects_JLDP_policy_at_preemption_point Job H0 H1 PState H2 jr arr_seq sched
  (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H policy))
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       forall {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
       JobPreemptable Job ->
       @JobReady Job PState H1 H0 -> arrival_sequence Job -> @schedule Job PState -> FP_policy Task -> Prop

Arguments respects_FP_policy_at_preemption_point {Task Job H H0 H1 PState H2 jr} arr_seq sched policy
```

## Lean

```lean
@Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [inst_3 : Prosa.Behavior.Job.JobArrival Job] →
            [inst_4 : Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                  [jr : Prosa.Behavior.Ready.JobReady Job PState] →
                    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                      Prosa.Behavior.Schedule.schedule PState → Prosa.Model.Priority.Definitions.FP_policy Task → Prop
```

Body:

```lean
def Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [inst_3 : Prosa.Behavior.Job.JobArrival Job] →
            [inst_4 : Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                  [jr : Prosa.Behavior.Ready.JobReady Job PState] →
                    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                      Prosa.Behavior.Schedule.schedule PState →
                        Prosa.Model.Priority.Definitions.FP_policy Task → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched
    policy =>
  Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point arr_seq sched
    Prosa.Model.Priority.Coercion.JLFP_to_JLDP
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
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
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0
Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
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
  (policy : Prosa_Model_Priority_Definitions_FP_policy Task
              inst_3) =>
Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point Job
  inst_7
  inst_14
  inst_17 PState
  inst_22 jr arr_seq sched
  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
     inst_7
     (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
        inst_7 Task
        inst_3
        inst_10 policy))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
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
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp

Arguments Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point 
  Task inst_3 Job
  inst_7
  inst_10
  inst_14
  inst_17 PState
  inst_22 jr arr_seq 
  sched policy
```
