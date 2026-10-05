# `scheduler_executes_job_with_earliest_arrival`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.sequential.scheduler_executes_job_with_earliest_arrival`
- Lean: `Prosa.Analysis.Facts.Model.Sequential.scheduler_executes_job_with_earliest_arrival`
- Certificate: `scheduler_executes_job_with_earliest_arrival_correspondence`

## Official Rocq

```coq
scheduler_executes_job_with_earliest_arrival :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job} 
  {H1 : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState),
@sequential_tasks Job Task H H0 H1 PState arr_seq sched ->
forall (j1 j2 : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
is_true (@same_task Job Task H j1 j2) ->
is_true (~~ @completed_by Job PState sched H1 j2 t) ->
is_true (@scheduled_at Job PState sched j1 t) -> is_true (@job_arrival Job H0 j1 <= @job_arrival Job H0 j2)

scheduler_executes_job_with_earliest_arrival is not universe polymorphic
Arguments scheduler_executes_job_with_earliest_arrival {Job Task H H0 H1 PState} 
  arr_seq sched H_sequential_tasks j1 j2 t _ _ _ _ _
scheduler_executes_job_with_earliest_arrival is opaque
Expands to: Constant prosa.analysis.facts.model.sequential.scheduler_executes_job_with_earliest_arrival
Declared in library prosa.analysis.facts.model.sequential, line 31, characters 12-56
@scheduler_executes_job_with_earliest_arrival
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState),
       @sequential_tasks Job Task H H0 H1 PState arr_seq sched ->
       forall (j1 j2 : Equality.sort Job) (t : instant),
       @arrives_in Job arr_seq j1 ->
       @arrives_in Job arr_seq j2 ->
       is_true (@same_task Job Task H j1 j2) ->
       is_true (~~ @completed_by Job PState sched H1 j2 t) ->
       is_true (@scheduled_at Job PState sched j1 t) ->
       is_true (@job_arrival Job H0 j1 <= @job_arrival Job H0 j2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sequential.scheduler_executes_job_with_earliest_arrival : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
    ∀ (j1 j2 : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
          Prosa.Model.Task.Concept.same_task j1 j2 = true →
            (!Prosa.Behavior.Service.completed_by sched j2 t) = true →
              Prosa.Behavior.Service.scheduled_at sched j1 t = true →
                Prosa.Behavior.Job.job_arrival j1 ≤ Prosa.Behavior.Job.job_arrival j2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sequential_scheduler_executes_job_with_earliest_arrival
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_10
         inst_14
         inst_17 PState arr_seq sched ->
       forall (j1 j2 : Job) (t : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j1 ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j2 ->
       @eq Bool
         (Prosa_Model_Task_Concept_same_task Job
            inst_3 Task
            inst_7
            inst_10 j1 j2)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_17 j2 t))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j1 t)
         Bool_true ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_14 j1)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_14 j2)
```
