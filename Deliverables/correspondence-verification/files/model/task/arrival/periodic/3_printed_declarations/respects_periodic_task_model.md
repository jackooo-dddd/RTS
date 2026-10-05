# `respects_periodic_task_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.periodic.respects_periodic_task_model`
- Lean: `Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model`
- Certificate: `respects_periodic_task_model_correspondence`

## Official Rocq

```coq
respects_periodic_task_model :
forall {Task : TaskType},
PeriodicModel Task ->
forall {Job : JobType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

respects_periodic_task_model is not universe polymorphic
Arguments respects_periodic_task_model {Task H Job H0 H1} arr_seq tsk
respects_periodic_task_model is transparent
Expands to: Constant prosa.model.task.arrival.periodic.respects_periodic_task_model
Declared in library prosa.model.task.arrival.periodic, line 40, characters 13-41
@respects_periodic_task_model
     : forall Task : TaskType,
       PeriodicModel Task ->
       forall Job : JobType,
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop
```

Body:

```coq
respects_periodic_task_model =
fun (Task : TaskType) (H : PeriodicModel Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_index Task Job H1 H0 arr_seq j) ->
@job_task Job Task H0 j = tsk ->
exists j' : Equality.sort Job,
  @arrives_in Job arr_seq j' /\
  @job_index Task Job H1 H0 arr_seq j' = @job_index Task Job H1 H0 arr_seq j - 1 /\
  @job_task Job Task H0 j' = tsk /\ @job_arrival Job H1 j = @job_arrival Job H1 j' + @task_period Task H tsk
     : forall {Task : TaskType},
       PeriodicModel Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

Arguments respects_periodic_task_model {Task H Job H0 H1} arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq tsk =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      0 < Prosa.Model.Task.Arrivals.job_index arr_seq j →
        Prosa.Model.Task.Concept.job_task j = tsk →
          ∃ j',
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' ∧
              Prosa.Model.Task.Arrivals.job_index arr_seq j' = Prosa.Model.Task.Arrivals.job_index arr_seq j - 1 ∧
                Prosa.Model.Task.Concept.job_task j' = tsk ∧
                  Prosa.Behavior.Job.job_arrival j =
                    Prosa.Behavior.Job.job_arrival j' + Prosa.Model.Task.Arrival.Periodic.task_period tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Arrival_Periodic_PeriodicModel
                                                                              Task
                                                                              inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask
                                                                               Job
                                                                               inst_10
                                                                               Task
                                                                               inst_3)
  (inst_17 : Prosa_Behavior_Job_JobArrival
                                                                               Job
                                                                               inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (tsk : Task) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_10 arr_seq j ->
LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (Prosa_Model_Task_Arrivals_job_index Task
     inst_3 Job
     inst_10
     inst_17
     inst_13 arr_seq j) ->
@eq Task
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_10 Task
     inst_3
     inst_13 j)
  tsk ->
Exists Job
  (fun j' : Job =>
   And
     (Prosa_Behavior_Arrival_sequence_arrives_in Job
        inst_10 arr_seq j')
     (And
        (@eq Nat
           (Prosa_Model_Task_Arrivals_job_index Task
              inst_3 Job
              inst_10
              inst_17
              inst_13 arr_seq j')
           (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
              (Prosa_Model_Task_Arrivals_job_index Task
                 inst_3 Job
                 inst_10
                 inst_17
                 inst_13 arr_seq j)
              (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
        (And
           (@eq Task
              (Prosa_Model_Task_Concept_JobTask_job_task Job
                 inst_10 Task
                 inst_3
                 inst_13 j')
              tsk)
           (@eq Prosa_Behavior_Time_instant
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_10
                 inst_17 j)
              (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                 (Prosa_Behavior_Job_JobArrival_job_arrival Job
                    inst_10
                    inst_17 j')
                 (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
                    inst_3
                    inst_6 tsk))))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp

Arguments Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 arr_seq 
  tsk
```
