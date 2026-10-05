# `EDF_implies_sequential_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.edf.EDF_implies_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Edf.EDF_implies_sequential_tasks`
- Certificate: `EDF_implies_sequential_tasks_correspondence`

## Official Rocq

```coq
EDF_implies_sequential_tasks :
forall {Task : TaskType} {H0 : TaskDeadline Task} {Job : JobType} {H2 : JobTask Job Task}
  {Arrival : JobArrival Job} {Cost : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job Arrival arr_seq ->
forall (sched : @schedule Job PState) {H3 : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H3 arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H2)) ->
@valid_schedule Job Arrival PState sched Cost H3 arr_seq ->
forall {H4 : JobPreemptable Job},
@valid_preemption_model Job Cost H4 PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H4 H3 arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H2)) ->
@sequential_tasks Job Task H2 Arrival Cost PState arr_seq sched

EDF_implies_sequential_tasks is not universe polymorphic
Arguments EDF_implies_sequential_tasks {Task H0 Job H2 Arrival Cost PState} H_uniproc 
  arr_seq H_valid_arrivals sched {H3} H_job_ready H_sched_valid {H4} H_valid_preemption_model
  H_respects_policy j1 j2 t _ _ _ _ _
EDF_implies_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.edf.EDF_implies_sequential_tasks
Declared in library prosa.analysis.facts.priority.edf, line 133, characters 8-36
@EDF_implies_sequential_tasks
     : forall (Task : TaskType) (H0 : TaskDeadline Task) (Job : JobType) (H2 : JobTask Job Task)
         (Arrival : JobArrival Job) (Cost : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (sched : @schedule Job PState) (H3 : @JobReady Job PState Cost Arrival),
       @work_bearing_readiness Job Arrival Cost PState H3 arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H2)) ->
       @valid_schedule Job Arrival PState sched Cost H3 arr_seq ->
       forall H4 : JobPreemptable Job,
       @valid_preemption_model Job Cost H4 PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H4 H3 arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H2)) ->
       @sequential_tasks Job Task H2 Arrival Cost PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Edf.EDF_implies_sequential_tasks : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [inst_6 : Prosa.Behavior.Ready.JobReady Job PState],
          Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              ∀ [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                  Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                      (Prosa.Model.Priority.Edf.EDF Job) →
                    Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Edf_EDF_implies_sequential_tasks
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_17 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_41 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_20
            inst_17),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_17
         inst_20 PState
         inst_41 arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_3
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_3
               inst_7
               inst_10
               inst_17
               inst_13)) ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_17 PState sched
         inst_20
         inst_41 arr_seq ->
       forall
         inst_66 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_20
         inst_66 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_17
         inst_20 PState
         inst_66
         inst_41 arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_3
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_3
               inst_7
               inst_10
               inst_17
               inst_13)) ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_13
         inst_17
         inst_20 PState arr_seq sched
```
