# `respects_TDMA_policy`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.respects_TDMA_policy`
- Lean: `Prosa.Model.Schedule.Tdma.respects_TDMA_policy`
- Certificate: `respects_TDMA_policy_correspondence`

## Official Rocq

```coq
respects_TDMA_policy :
forall {Task : TaskType} {Job : JobType} {PState : ProcessorState Job} {ja : JobArrival Job}
  {jc : JobCost Job},
@JobReady Job PState jc ja ->
JobTask Job Task ->
arrival_sequence Job -> @schedule Job PState -> {setEquality.sort Task} -> TDMAPolicy Task -> Prop

respects_TDMA_policy is not universe polymorphic
Arguments respects_TDMA_policy {Task Job PState ja jc jr H} arr_seq sched ts {H0}
respects_TDMA_policy is transparent
Expands to: Constant prosa.model.schedule.tdma.respects_TDMA_policy
Declared in library prosa.model.schedule.tdma, line 156, characters 13-33
@respects_TDMA_policy
     : forall (Task : TaskType) (Job : JobType) (PState : ProcessorState Job) (ja : JobArrival Job)
         (jc : JobCost Job),
       @JobReady Job PState jc ja ->
       JobTask Job Task ->
       arrival_sequence Job -> @schedule Job PState -> {setEquality.sort Task} -> TDMAPolicy Task -> Prop
```

Body:

```coq
respects_TDMA_policy =
fun (Task : TaskType) (Job : JobType) (PState : ProcessorState Job) (ja : JobArrival Job) 
  (jc : JobCost Job) (jr : @JobReady Job PState jc ja) (H : JobTask Job Task)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (ts : {setEquality.sort Task})
  (H0 : TDMAPolicy Task) =>
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
@sched_implies_in_slot Task Job PState H sched ts H0 j t /\
@backlogged_implies_not_in_slot_or_other_job_sched Task Job PState ja jc jr H arr_seq sched ts H0 j t
     : forall {Task : TaskType} {Job : JobType} {PState : ProcessorState Job} {ja : JobArrival Job}
         {jc : JobCost Job},
       @JobReady Job PState jc ja ->
       JobTask Job Task ->
       arrival_sequence Job -> @schedule Job PState -> {setEquality.sort Task} -> TDMAPolicy Task -> Prop

Arguments respects_TDMA_policy {Task Job PState ja jc jr H} arr_seq sched ts {H0}
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.respects_TDMA_policy : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              [inst_4 : Prosa.Behavior.Job.JobArrival Job] →
                [inst_5 : Prosa.Behavior.Job.JobCost Job] →
                  [Prosa.Behavior.Ready.JobReady Job PState] →
                    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                      Prosa.Behavior.Schedule.schedule PState → Prosa.Util.Seqset.set Task → Prop
def Prosa.Model.Schedule.Tdma.respects_TDMA_policy.{u_1, u_2, u_3, u_4} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              [inst_4 : Prosa.Behavior.Job.JobArrival Job] →
                [inst_5 : Prosa.Behavior.Job.JobCost Job] →
                  [Prosa.Behavior.Ready.JobReady Job PState] →
                    Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                      Prosa.Behavior.Schedule.schedule PState → Prosa.Util.Seqset.set Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] {PState} [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Ready.JobReady Job PState] arrSeq sched ts =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j →
      Prosa.Model.Schedule.Tdma.sched_implies_in_slot sched ts j t ∧
        Prosa.Model.Schedule.Tdma.backlogged_implies_not_in_slot_or_other_job_sched arrSeq sched ts j t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_respects_TDMA_policy
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_10)
         (inst_19 : Prosa_Behavior_Job_JobArrival Job
                                                                              inst_10)
         (inst_22 : Prosa_Behavior_Job_JobCost Job
                                                                              inst_10),
       Prosa_Behavior_Ready_JobReady Job inst_10
         PState inst_22
         inst_19 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job inst_10
         PState ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp
```

Body:

```coq
Prosa_Model_Schedule_Tdma_respects_TDMA_policy@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.max__u_2+1_u_3+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                      inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask Job
                                                                       inst_10
                                                                       Task
                                                                       inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_10)
  (inst_19 : Prosa_Behavior_Job_JobArrival Job
                                                                       inst_10)
  (inst_22 : Prosa_Behavior_Job_JobCost Job
                                                                       inst_10)
  (inst_25 : Prosa_Behavior_Ready_JobReady Job
                                                                       inst_10
                                                                       PState
                                                                       inst_22
                                                                       inst_19)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_10)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_10 PState)
  (ts : Prosa_Util_Seqset_set Task inst_3) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_10 arrSeq j ->
And
  (Prosa_Model_Schedule_Tdma_sched_implies_in_slot Task
     inst_3
     inst_6 Job
     inst_10
     inst_13 PState sched ts j t)
  (Prosa_Model_Schedule_Tdma_backlogged_implies_not_in_slot_or_other_job_sched Task
     inst_3
     inst_6 Job
     inst_10
     inst_13 PState
     inst_19
     inst_22
     inst_25 arrSeq sched ts j t)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_10)
         (inst_19 : Prosa_Behavior_Job_JobArrival Job
                                                                              inst_10)
         (inst_22 : Prosa_Behavior_Job_JobCost Job
                                                                              inst_10),
       Prosa_Behavior_Ready_JobReady Job inst_10
         PState inst_22
         inst_19 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job inst_10
         PState ->
       Prosa_Util_Seqset_set Task inst_3 -> SProp

Arguments Prosa_Model_Schedule_Tdma_respects_TDMA_policy Task
  inst_3
  inst_6 Job
  inst_10
  inst_13 PState
  inst_19
  inst_22
  inst_25 arrSeq sched ts
```
