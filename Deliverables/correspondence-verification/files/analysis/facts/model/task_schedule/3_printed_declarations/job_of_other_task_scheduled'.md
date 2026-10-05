# `job_of_other_task_scheduled'`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled'`
- Lean: `Prosa.Analysis.Facts.Model.TaskSchedule.job_of_other_task_scheduled'`
- Certificate: `job_of_other_task_scheduled'_correspondence`

## Official Rocq

```coq
job_of_other_task_scheduled' :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t : instant),
is_true (~~ @job_of_task Job Task H0 tsk j) ->
is_true (@scheduled_at Job PState sched j t) ->
is_true (~~ @task_served_at Task Job H0 arr_seq PState sched tsk t)

job_of_other_task_scheduled' is not universe polymorphic
Arguments job_of_other_task_scheduled' {Task Job H0 H1} arr_seq H_valid_arrivals 
  {PState} H_uniproc sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute 
  tsk j t _ _
job_of_other_task_scheduled' is opaque
Expands to: Constant prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled'
Declared in library prosa.analysis.facts.model.task_schedule, line 132, characters 12-40
@job_of_other_task_scheduled'
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t : instant),
       is_true (~~ @job_of_task Job Task H0 tsk j) ->
       is_true (@scheduled_at Job PState sched j t) ->
       is_true (~~ @task_served_at Task Job H0 arr_seq PState sched tsk t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskSchedule.job_of_other_task_scheduled' : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
            Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
              ∀ (tsk : Task) (j : Job) (t : Prosa.Behavior.Time.instant),
                (!Prosa.Model.Task.Concept.job_of_task tsk j) = true →
                  Prosa.Behavior.Service.scheduled_at sched j t = true →
                    (!Prosa.Analysis.Definitions.TaskSchedule.task_served_at arr_seq sched tsk t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskSchedule_job_of_other_task_scheduled'
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_14 PState sched ->
       forall (tsk : Task) (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Model_Task_Concept_job_of_task Job
               inst_7 Task
               inst_3
               inst_10 tsk j))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_7 PState sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_TaskSchedule_task_served_at Task
               inst_3 Job
               inst_7
               inst_10 PState arr_seq
               sched tsk t))
         Bool_true
```
