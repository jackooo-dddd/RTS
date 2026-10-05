# `prior_jobs_complete`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.sequentiality.prior_jobs_complete`
- Lean: `Prosa.Model.Task.Sequentiality.prior_jobs_complete`
- Certificate: `prior_jobs_complete_correspondence`

## Official Rocq

```coq
prior_jobs_complete :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

prior_jobs_complete is not universe polymorphic
Arguments prior_jobs_complete {Job Task H H0 H1 PState} arr_seq sched j t
prior_jobs_complete is transparent
Expands to: Constant prosa.model.task.sequentiality.prior_jobs_complete
Declared in library prosa.model.task.sequentiality, line 42, characters 13-32
@prior_jobs_complete
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
prior_jobs_complete =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant) =>
@all (Equality.sort Job) ((@completed_by Job PState sched H1)^~ t)
  (@task_arrivals_before Job Task H arr_seq (@job_task Job Task H j) (@job_arrival Job H0 j))
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments prior_jobs_complete {Job Task H H0 H1 PState} arr_seq sched j t
```

## Lean

```lean
@Prosa.Model.Task.Sequentiality.prior_jobs_complete : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Task.Sequentiality.prior_jobs_complete.{u_1, u_2, u_3, u_4} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched j t =>
  (Prosa.Model.Task.Arrivals.task_arrivals_before arr_seq (Prosa.Model.Task.Concept.job_task j)
        (Prosa.Behavior.Job.job_arrival j)).all
    fun j_tsk => Prosa.Behavior.Service.completed_by sched j_tsk t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Sequentiality_prior_jobs_complete
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Task_Sequentiality_prior_jobs_complete@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_3+2_u_4+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0
Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                            Job
                                                                            inst_3
                                                                            Task
                                                                            inst_7)
  (inst_14 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (inst_17 : Prosa_Behavior_Job_JobCost Job
                                                                            inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
List_all Job
  (Prosa_Model_Task_Arrivals_task_arrivals_before Job
     inst_3 Task
     inst_7
     inst_10 arr_seq
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j)
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_14 j))
  (fun j_tsk : Job =>
   Prosa_Behavior_Service_completed_by Job
     inst_3 PState sched
     inst_17 j_tsk t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Task_Sequentiality_prior_jobs_complete Job
  inst_3 Task
  inst_7
  inst_10
  inst_14
  inst_17 PState arr_seq 
  sched j t
```
