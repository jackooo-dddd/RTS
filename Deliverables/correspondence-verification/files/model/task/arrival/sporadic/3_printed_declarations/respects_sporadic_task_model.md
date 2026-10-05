# `respects_sporadic_task_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.sporadic.respects_sporadic_task_model`
- Lean: `Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model`
- Certificate: `sp_respects_sporadic_task_model_canonical`

## Official Rocq

```coq
respects_sporadic_task_model :
forall {Task : TaskType},
SporadicModel Task ->
forall {Job : JobType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

respects_sporadic_task_model is not universe polymorphic
Arguments respects_sporadic_task_model {Task H Job H0 H1} arr_seq tsk
respects_sporadic_task_model is transparent
Expands to: Constant prosa.model.task.arrival.sporadic.respects_sporadic_task_model
Declared in library prosa.model.task.arrival.sporadic, line 47, characters 13-41
@respects_sporadic_task_model
     : forall Task : TaskType,
       SporadicModel Task ->
       forall Job : JobType,
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop
```

Body:

```coq
respects_sporadic_task_model =
fun (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) =>
forall j j' : Equality.sort Job,
j <> j' ->
@arrives_in Job arr_seq j ->
@arrives_in Job arr_seq j' ->
@job_task Job Task H0 j = tsk ->
@job_task Job Task H0 j' = tsk ->
is_true (@job_arrival Job H1 j <= @job_arrival Job H1 j') ->
is_true (@job_arrival Job H1 j + @task_min_inter_arrival_time Task H tsk <= @job_arrival Job H1 j')
     : forall {Task : TaskType},
       SporadicModel Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

Arguments respects_sporadic_task_model {Task H Job H0 H1} arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop
def Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq tsk =>
  ∀ (j j' : Job),
    j ≠ j' →
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' →
          Prosa.Model.Task.Concept.job_task j = tsk →
            Prosa.Model.Task.Concept.job_task j' = tsk →
              Prosa.Behavior.Job.job_arrival j ≤ Prosa.Behavior.Job.job_arrival j' →
                Prosa.Behavior.Job.job_arrival j + Prosa.Model.Task.Arrival.Sporadic.task_min_inter_arrival_time tsk ≤
                  Prosa.Behavior.Job.job_arrival j'
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_12 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_12 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_12 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_12 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Arrival_Sporadic_SporadicModel
                                                                              Task
                                                                              inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_12 : DecidableEq Job)
  (inst_15 : Prosa_Model_Task_Concept_JobTask
                                                                               Job
                                                                               inst_12
                                                                               Task
                                                                               inst_3)
  (inst_19 : Prosa_Behavior_Job_JobArrival
                                                                               Job
                                                                               inst_12)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_12)
  (tsk : Task) =>
forall j j' : Job,
Ne Job j j' ->
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_12 arr_seq j ->
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_12 arr_seq j' ->
@eq Task
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_12 Task
     inst_3
     inst_15 j)
  tsk ->
@eq Task
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_12 Task
     inst_3
     inst_15 j')
  tsk ->
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_12
     inst_19 j)
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_12
     inst_19 j') ->
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_12
        inst_19 j)
     (Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task
        inst_3
        inst_6 tsk))
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_12
     inst_19 j')
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_12 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_12 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_12 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_12 ->
       Task -> SProp

Arguments Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model Task
  inst_3
  inst_6 Job
  inst_12
  inst_15
  inst_19 arr_seq 
  tsk
```
