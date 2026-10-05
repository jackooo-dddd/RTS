# `gel_generalizes_edf`

- Kind (Rocq): Remark
- Rocq: `prosa.results.generality.gel.gel_generalizes_edf`
- Lean: `Prosa.Results.Generality.Gel.gel_generalizes_edf`
- Certificate: `gel_generalizes_edf_correspondence`

## Official Rocq

```coq
gel_generalizes_edf :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {PState : ProcessorState Job} {Arrival : JobArrival Job} {Cost : JobCost Job} {H1 : JobPreemptable Job}
  {JR : @JobReady Job PState Cost Arrival} {H2 : TaskDeadline Task},
(forall tsk : Equality.sort Task, @task_priority_point Task H tsk = Posz (@task_deadline Task H2 tsk)) ->
forall (sched : @schedule Job PState) (arr_seq : arrival_sequence Job),
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
  (@GEL Job Task H Arrival H0) <->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H2 Arrival H0))

gel_generalizes_edf is not universe polymorphic
Arguments gel_generalizes_edf {Task H Job H0 PState Arrival Cost H1 JR H2} H_priority_point%function_scope
  sched arr_seq
gel_generalizes_edf is opaque
Expands to: Constant prosa.results.generality.gel.gel_generalizes_edf
Declared in library prosa.results.generality.gel, line 52, characters 11-30
@gel_generalizes_edf
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (PState : ProcessorState Job) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H1 : JobPreemptable Job) (JR : @JobReady Job PState Cost Arrival) (H2 : TaskDeadline Task),
       (forall tsk : Equality.sort Task, @task_priority_point Task H tsk = Posz (@task_deadline Task H2 tsk)) ->
       forall (sched : @schedule Job PState) (arr_seq : arrival_sequence Job),
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
         (@GEL Job Task H Arrival H0) <->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H2 Arrival H0))
```

## Lean

```lean
@Prosa.Results.Generality.Gel.gel_generalizes_edf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [Arrival : Prosa.Behavior.Job.JobArrival Job]
  [Cost : Prosa.Behavior.Job.JobCost Job] [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  [JR : Prosa.Behavior.Ready.JobReady Job PState] [inst_5 : Prosa.Model.Task.Concept.TaskDeadline Task],
  (∀ (tsk : Task), Prosa.Model.Priority.Gel.task_priority_point tsk = ↑(Prosa.Model.Task.Concept.task_deadline tsk)) →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState)
      (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
          (Prosa.Model.Priority.Gel.GEL Job Task) ↔
        Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
          (Prosa.Model.Priority.Edf.EDF Job)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Generality_Gel_gel_generalizes_edf
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
                 inst_7 PState Cost Arrival)
         (inst_29 : Prosa_Model_Task_Concept_TaskDeadline
                                                                                Task
                                                                                inst_3),
       (forall tsk : Task,
        @eq Prosa_Model_Priority_Gel_offset
          (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
             inst_3
             inst_10 tsk)
          (Nat_cast_inst1 Int instNatCastInt
             (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                inst_3
                inst_29 tsk))) ->
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
            (Prosa_Model_Priority_Edf_EDF Job
               inst_7
               (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                  inst_7
                  inst_3
                  inst_29 Arrival
                  inst_13)))
```
