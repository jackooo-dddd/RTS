# `GEL_implies_sequential_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.gel.GEL_implies_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Gel.GEL_implies_sequential_tasks`
- Certificate: `GEL_implies_sequential_tasks_correspondence`

## Official Rocq

```coq
GEL_implies_sequential_tasks :
forall {Task : concept.TaskType} {Job : job.JobType} {H : concept.JobTask Job Task}
  {H0 : gel.PriorityPoint Task} {Arrival : job.JobArrival Job} {H1 : job.JobCost Job}
  (arr_seq : arrival_sequence.arrival_sequence Job),
@arrival_sequence.valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : schedule.ProcessorState Job},
@platform_properties.uniprocessor_model Job PState ->
forall (sched : @schedule.schedule Job PState) {JobReady0 : @ready.JobReady Job PState H1 Arrival},
@work_bearing_readiness.work_bearing_readiness Job Arrival H1 PState JobReady0 arr_seq sched
  (@gel.GEL Job Task H0 Arrival H) ->
@ready.valid_schedule Job Arrival PState sched H1 JobReady0 arr_seq ->
forall {H2 : parameter.JobPreemptable Job},
@parameter.valid_preemption_model Job H1 H2 PState arr_seq sched ->
@priority_driven.respects_JLFP_policy_at_preemption_point Job Arrival H1 PState H2 JobReady0 arr_seq sched
  (@gel.GEL Job Task H0 Arrival H) ->
@sequentiality.sequential_tasks Job Task H Arrival H1 PState arr_seq sched

GEL_implies_sequential_tasks is not universe polymorphic
Arguments GEL_implies_sequential_tasks {Task Job H H0 Arrival H1} arr_seq H_valid_arrivals 
  {PState} H_uniproc sched {JobReady0} H_job_ready H_sched_valid {H2} H_valid_preemption_model
  H_respects_policy j1 j2 t _ _ _ _ _
GEL_implies_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.gel.GEL_implies_sequential_tasks
Declared in library prosa.analysis.facts.priority.gel, line 110, characters 10-38
@GEL_implies_sequential_tasks
     : forall (Task : concept.TaskType) (Job : job.JobType) (H : concept.JobTask Job Task)
         (H0 : gel.PriorityPoint Task) (Arrival : job.JobArrival Job) (H1 : job.JobCost Job)
         (arr_seq : arrival_sequence.arrival_sequence Job),
       @arrival_sequence.valid_arrival_sequence Job Arrival arr_seq ->
       forall PState : schedule.ProcessorState Job,
       @platform_properties.uniprocessor_model Job PState ->
       forall (sched : @schedule.schedule Job PState) (JobReady0 : @ready.JobReady Job PState H1 Arrival),
       @work_bearing_readiness.work_bearing_readiness Job Arrival H1 PState JobReady0 arr_seq sched
         (@gel.GEL Job Task H0 Arrival H) ->
       @ready.valid_schedule Job Arrival PState sched H1 JobReady0 arr_seq ->
       forall H2 : parameter.JobPreemptable Job,
       @parameter.valid_preemption_model Job H1 H2 PState arr_seq sched ->
       @priority_driven.respects_JLFP_policy_at_preemption_point Job Arrival H1 PState H2 JobReady0 arr_seq
         sched (@gel.GEL Job Task H0 Arrival H) ->
       @sequentiality.sequential_tasks Job Task H Arrival H1 PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Gel.GEL_implies_sequential_tasks : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  [Arrival : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [JobReady0 : Prosa.Behavior.Ready.JobReady Job PState],
          Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              ∀ [inst_5 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                  Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                      (Prosa.Model.Priority.Gel.GEL Job Task) →
                    Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Gel_GEL_implies_sequential_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Arrival : Prosa_Behavior_Job_JobArrival Job
                      inst_7)
         (inst_19 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7 Arrival arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (JobReady0 : Prosa_Behavior_Ready_JobReady Job
                        inst_7 PState
                        inst_19 Arrival),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_7 Arrival
         inst_19 PState JobReady0 arr_seq
         sched
         (Prosa_Model_Priority_Gel_GEL Job
            inst_7 Task
            inst_3
            inst_14 Arrival
            inst_10) ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7 Arrival PState sched
         inst_19 JobReady0 arr_seq ->
       forall
         inst_61 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_7
         inst_19
         inst_61 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_7 Arrival
         inst_19 PState
         inst_61 JobReady0 arr_seq sched
         (Prosa_Model_Priority_Gel_GEL Job
            inst_7 Task
            inst_3
            inst_14 Arrival
            inst_10) ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_10 Arrival
         inst_19 PState arr_seq sched
```
