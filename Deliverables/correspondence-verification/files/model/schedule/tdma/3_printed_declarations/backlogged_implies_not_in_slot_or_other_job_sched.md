# `backlogged_implies_not_in_slot_or_other_job_sched`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.backlogged_implies_not_in_slot_or_other_job_sched`
- Lean: `Prosa.Model.Schedule.Tdma.backlogged_implies_not_in_slot_or_other_job_sched`
- Certificate: `backlogged_implies_not_in_slot_or_other_job_sched_correspondence`

## Official Rocq

```coq
backlogged_implies_not_in_slot_or_other_job_sched :
forall {Task : TaskType} {Job : JobType} {PState : ProcessorState Job} {ja : JobArrival Job}
  {jc : JobCost Job},
@JobReady Job PState jc ja ->
JobTask Job Task ->
arrival_sequence Job ->
@schedule Job PState -> {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> Prop

backlogged_implies_not_in_slot_or_other_job_sched is not universe polymorphic
Arguments backlogged_implies_not_in_slot_or_other_job_sched {Task Job PState ja jc jr H} 
  arr_seq sched ts {H0} j t
backlogged_implies_not_in_slot_or_other_job_sched is transparent
Expands to: Constant prosa.model.schedule.tdma.backlogged_implies_not_in_slot_or_other_job_sched
Declared in library prosa.model.schedule.tdma, line 146, characters 13-62
@backlogged_implies_not_in_slot_or_other_job_sched
     : forall (Task : TaskType) (Job : JobType) (PState : ProcessorState Job) (ja : JobArrival Job)
         (jc : JobCost Job),
       @JobReady Job PState jc ja ->
       JobTask Job Task ->
       arrival_sequence Job ->
       @schedule Job PState ->
       {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> Prop
```

Body:

```coq
backlogged_implies_not_in_slot_or_other_job_sched =
fun (Task : TaskType) (Job : JobType) (PState : ProcessorState Job) (ja : JobArrival Job) 
  (jc : JobCost Job) (jr : @JobReady Job PState jc ja) (H : JobTask Job Task)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (ts : {setEquality.sort Task})
  (H0 : TDMAPolicy Task) (j : Equality.sort Job) (t : instant) =>
is_true (@backlogged Job PState jc ja jr sched j t) ->
~ is_true (@job_in_time_slot Task Job H ts H0 j t) \/
(exists j_other : Equality.sort Job,
   @arrives_in Job arr_seq j_other /\
   is_true (@job_arrival Job ja j_other < @job_arrival Job ja j) /\
   @job_task Job Task H j = @job_task Job Task H j_other /\
   is_true (@scheduled_at Job PState sched j_other t))
     : forall {Task : TaskType} {Job : JobType} {PState : ProcessorState Job} {ja : JobArrival Job}
         {jc : JobCost Job},
       @JobReady Job PState jc ja ->
       JobTask Job Task ->
       arrival_sequence Job ->
       @schedule Job PState ->
       {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> Prop

Arguments backlogged_implies_not_in_slot_or_other_job_sched {Task Job PState ja jc jr H} 
  arr_seq sched ts {H0} j t
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.backlogged_implies_not_in_slot_or_other_job_sched : {Task :
    Prosa.Model.Task.Concept.TaskType} →
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
                      Prosa.Behavior.Schedule.schedule PState →
                        Prosa.Util.Seqset.set Task → Job → Prosa.Behavior.Time.instant → Prop
def Prosa.Model.Schedule.Tdma.backlogged_implies_not_in_slot_or_other_job_sched.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
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
                      Prosa.Behavior.Schedule.schedule PState →
                        Prosa.Util.Seqset.set Task → Job → Prosa.Behavior.Time.instant → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] {PState} [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Ready.JobReady Job PState] arrSeq sched ts j t =>
  Prosa.Behavior.Ready.backlogged sched j t = true →
    ¬Prosa.Model.Schedule.Tdma.job_in_time_slot ts j t = true ∨
      ∃ jOther,
        Prosa.Behavior.Arrival_sequence.arrives_in arrSeq jOther ∧
          Prosa.Behavior.Job.job_arrival jOther < Prosa.Behavior.Job.job_arrival j ∧
            Prosa.Model.Task.Concept.job_task j = Prosa.Model.Task.Concept.job_task jOther ∧
              Prosa.Behavior.Service.scheduled_at sched jOther t = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_backlogged_implies_not_in_slot_or_other_job_sched
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
       Prosa_Util_Seqset_set Task inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Model_Schedule_Tdma_backlogged_implies_not_in_slot_or_other_job_sched@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0
Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
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
  (ts : Prosa_Util_Seqset_set Task inst_3) 
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
@eq Bool
  (Prosa_Behavior_Ready_backlogged Job inst_10 PState
     inst_22
     inst_19
     inst_25 sched j t)
  Bool_true ->
Or
  (Not
     (@eq Bool
        (Prosa_Model_Schedule_Tdma_job_in_time_slot Task
           inst_3
           inst_6 Job
           inst_10
           inst_13 ts j t)
        Bool_true))
  (Exists Job
     (fun jOther : Job =>
      And
        (Prosa_Behavior_Arrival_sequence_arrives_in Job
           inst_10 arrSeq jOther)
        (And
           (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_10
                 inst_19 jOther)
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_10
                 inst_19 j))
           (And
              (@eq Task
                 (Prosa_Model_Task_Concept_JobTask_job_task Job
                    inst_10 Task
                    inst_3
                    inst_13 j)
                 (Prosa_Model_Task_Concept_JobTask_job_task Job
                    inst_10 Task
                    inst_3
                    inst_13 jOther))
              (@eq Bool
                 (Prosa_Behavior_Service_scheduled_at Job
                    inst_10 PState sched jOther t)
                 Bool_true)))))
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
       Prosa_Util_Seqset_set Task inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Model_Schedule_Tdma_backlogged_implies_not_in_slot_or_other_job_sched 
  Task inst_3
  inst_6 Job
  inst_10
  inst_13 PState
  inst_19
  inst_22
  inst_25 arrSeq sched ts 
  j t
```
