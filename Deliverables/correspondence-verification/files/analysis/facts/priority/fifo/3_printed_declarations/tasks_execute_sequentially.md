# `tasks_execute_sequentially`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.fifo.tasks_execute_sequentially`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.tasks_execute_sequentially`
- Certificate: `tasks_execute_sequentially_correspondence`

## Official Rocq

```coq
tasks_execute_sequentially :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall sched : @schedule Job PState,
@valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
forall {H : JobPreemptable Job},
@valid_preemption_model Job Cost H PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H
  (@basic_ready_instance Job PState Arrival Cost) arr_seq sched (@FIFO Job Arrival) ->
forall {Task : TaskType} {H0 : JobTask Job Task},
@sequential_tasks Job Task H0 Arrival Cost PState arr_seq sched

tasks_execute_sequentially is not universe polymorphic
Arguments tasks_execute_sequentially {Job Arrival Cost} arr_seq H_valid_arrivals 
  {PState} H_uniproc sched H_schedule_is_valid {H} H_valid_preemption_model H_respects_policy 
  {Task H0} j1 j2 t _ _ _ _ _
tasks_execute_sequentially is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.tasks_execute_sequentially
Declared in library prosa.analysis.facts.priority.fifo, line 190, characters 10-36
@tasks_execute_sequentially
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall sched : @schedule Job PState,
       @valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
       forall H : JobPreemptable Job,
       @valid_preemption_model Job Cost H PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H
         (@basic_ready_instance Job PState Arrival Cost) arr_seq sched (@FIFO Job Arrival) ->
       forall (Task : TaskType) (H0 : JobTask Job Task),
       @sequential_tasks Job Task H0 Arrival Cost PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.tasks_execute_sequentially : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                    (Prosa.Model.Priority.Fifo.FIFO Job) →
                  ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst_4 : DecidableEq Task]
                    [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task],
                    Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_tasks_execute_sequentially
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_6
            inst_9)
         arr_seq ->
       forall
         inst_41 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_41 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_41
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_6
            inst_9)
         arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_3
            inst_6) ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_62 : DecidableEq Task)
         (inst_65 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_62),
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_3 Task
         inst_62
         inst_65
         inst_6
         inst_9 PState arr_seq sched
```
