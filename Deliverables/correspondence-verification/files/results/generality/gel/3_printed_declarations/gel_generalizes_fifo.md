# `gel_generalizes_fifo`

- Kind (Rocq): Remark
- Rocq: `prosa.results.generality.gel.gel_generalizes_fifo`
- Lean: `Prosa.Results.Generality.Gel.gel_generalizes_fifo`
- Certificate: `gel_generalizes_fifo_correspondence`

## Official Rocq

```coq
gel_generalizes_fifo :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {PState : ProcessorState Job} {Arrival : JobArrival Job} {Cost : JobCost Job} {H1 : JobPreemptable Job}
  {JR : @JobReady Job PState Cost Arrival},
(forall tsk : Equality.sort Task, @task_priority_point Task H tsk = 0%Z) ->
forall (sched : @schedule Job PState) (arr_seq : arrival_sequence Job),
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
  (@GEL Job Task H Arrival H0) <->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched (@FIFO Job Arrival)

gel_generalizes_fifo is not universe polymorphic
Arguments gel_generalizes_fifo {Task H Job H0 PState Arrival Cost H1 JR} H_priority_point%function_scope
  sched arr_seq
gel_generalizes_fifo is opaque
Expands to: Constant prosa.results.generality.gel.gel_generalizes_fifo
Declared in library prosa.results.generality.gel, line 78, characters 11-31
@gel_generalizes_fifo
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (PState : ProcessorState Job) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H1 : JobPreemptable Job) (JR : @JobReady Job PState Cost Arrival),
       (forall tsk : Equality.sort Task, @task_priority_point Task H tsk = 0%Z) ->
       forall (sched : @schedule Job PState) (arr_seq : arrival_sequence Job),
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
         (@GEL Job Task H Arrival H0) <->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
         (@FIFO Job Arrival)
```

## Lean

```lean
@Prosa.Results.Generality.Gel.gel_generalizes_fifo : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [Arrival : Prosa.Behavior.Job.JobArrival Job]
  [Cost : Prosa.Behavior.Job.JobCost Job] [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  [JR : Prosa.Behavior.Ready.JobReady Job PState],
  (∀ (tsk : Task), Prosa.Model.Priority.Gel.task_priority_point tsk = 0) →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState)
      (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
          (Prosa.Model.Priority.Gel.GEL Job Task) ↔
        Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
          (Prosa.Model.Priority.Fifo.FIFO Job)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Generality_Gel_gel_generalizes_fifo
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Priority_Gel_PriorityPoint
                                                                                Task
                                                                                inst_3)
         (inst_13 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (Arrival : Prosa_Behavior_Job_JobArrival Job
                      inst_7)
         (Cost : Prosa_Behavior_Job_JobCost Job
                   inst_7)
         (inst_23 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                                Job
                                                                                inst_7)
         (JR : Prosa_Behavior_Ready_JobReady Job
                 inst_7 PState Cost Arrival),
       (forall tsk : Task,
        @eq Prosa_Model_Priority_Gel_offset
          (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
             inst_3
             inst_10 tsk)
          (OfNat_ofNat_inst1 Prosa_Model_Priority_Gel_offset 0 (instOfNat 0))) ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Iff
         (Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
            inst_7 Arrival Cost PState
            inst_23 JR arr_seq sched
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_10 Arrival
               inst_13))
         (Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
            inst_7 Arrival Cost PState
            inst_23 JR arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7 Arrival))
```
