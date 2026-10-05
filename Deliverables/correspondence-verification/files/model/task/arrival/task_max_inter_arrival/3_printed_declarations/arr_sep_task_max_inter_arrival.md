# `arr_sep_task_max_inter_arrival`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.task_max_inter_arrival.arr_sep_task_max_inter_arrival`
- Lean: `Prosa.Model.Task.Arrival.Task_max_inter_arrival.arr_sep_task_max_inter_arrival`
- Certificate: `arr_sep_task_max_inter_arrival_correspondence`

## Official Rocq

```coq
arr_sep_task_max_inter_arrival :
forall {Task : TaskType},
TaskMaxInterArrival Task ->
forall {Job : JobType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

arr_sep_task_max_inter_arrival is not universe polymorphic
Arguments arr_sep_task_max_inter_arrival {Task H Job H0 H1} arr_seq tsk
arr_sep_task_max_inter_arrival is transparent
Expands to: Constant prosa.model.task.arrival.task_max_inter_arrival.arr_sep_task_max_inter_arrival
Declared in library prosa.model.task.arrival.task_max_inter_arrival, line 35, characters 13-43
@arr_sep_task_max_inter_arrival
     : forall Task : TaskType,
       TaskMaxInterArrival Task ->
       forall Job : JobType,
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop
```

Body:

```coq
arr_sep_task_max_inter_arrival =
fun (Task : TaskType) (H : TaskMaxInterArrival Task) (Job : JobType) (H0 : JobTask Job Task)
  (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
@job_task Job Task H0 j = tsk ->
is_true (0 < @job_index Task Job H1 H0 arr_seq j) ->
exists j' : Equality.sort Job,
  j <> j' /\
  @arrives_in Job arr_seq j' /\
  @job_task Job Task H0 j' = tsk /\
  is_true
    (@job_arrival Job H1 j' <= @job_arrival Job H1 j <=
     @job_arrival Job H1 j' + @task_max_inter_arrival_time Task H tsk)
     : forall {Task : TaskType},
       TaskMaxInterArrival Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

Arguments arr_sep_task_max_inter_arrival {Task H Job H0 H1} arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Task_max_inter_arrival.arr_sep_task_max_inter_arrival : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop
def Prosa.Model.Task.Arrival.Task_max_inter_arrival.arr_sep_task_max_inter_arrival.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] {Job}
    [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq tsk =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Task.Concept.job_task j = tsk →
        0 < Prosa.Model.Task.Arrivals.job_index arr_seq j →
          ∃ j',
            j ≠ j' ∧
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' ∧
                Prosa.Model.Task.Concept.job_task j' = tsk ∧
                  (decide (Prosa.Behavior.Job.job_arrival j' ≤ Prosa.Behavior.Job.job_arrival j) &&
                      decide
                        (Prosa.Behavior.Job.job_arrival j ≤
                          Prosa.Behavior.Job.job_arrival j' +
                            Prosa.Model.Task.Arrival.Task_max_inter_arrival.task_max_inter_arrival_time tsk)) =
                    true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Task_max_inter_arrival_arr_sep_task_max_inter_arrival
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
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
Prosa_Model_Task_Arrival_Task_max_inter_arrival_arr_sep_task_max_inter_arrival@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_10 Task
     inst_3)
  (inst_17 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (tsk : Task) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_10 arr_seq j ->
@eq Task
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_10 Task
     inst_3
     inst_13 j)
  tsk ->
LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (Prosa_Model_Task_Arrivals_job_index Task
     inst_3 Job
     inst_10
     inst_17
     inst_13 arr_seq j) ->
Exists Job
  (fun j' : Job =>
   And (Ne Job j j')
     (And
        (Prosa_Behavior_Arrival_sequence_arrives_in Job
           inst_10 arr_seq j')
        (And
           (@eq Task
              (Prosa_Model_Task_Concept_JobTask_job_task Job
                 inst_10 Task
                 inst_3
                 inst_13 j')
              tsk)
           (@eq Bool
              (Bool_and
                 (Decidable_decide
                    (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                       (Prosa_Behavior_Job_JobArrival_job_arrival Job
                          inst_10
                          inst_17
                          j')
                       (Prosa_Behavior_Job_JobArrival_job_arrival Job
                          inst_10
                          inst_17
                          j))
                    (Nat_decLe
                       (Prosa_Behavior_Job_JobArrival_job_arrival Job
                          inst_10
                          inst_17
                          j')
                       (Prosa_Behavior_Job_JobArrival_job_arrival Job
                          inst_10
                          inst_17
                          j)))
                 (Decidable_decide
                    (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                       (Prosa_Behavior_Job_JobArrival_job_arrival Job
                          inst_10
                          inst_17
                          j)
                       (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                          (Prosa_Behavior_Job_JobArrival_job_arrival Job
                             inst_10
                             inst_17
                             j')
                          (Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_task_max_inter_arrival_time
                             Task
                             inst_3
                             inst_6
                             tsk)))
                    (Nat_decLe
                       (Prosa_Behavior_Job_JobArrival_job_arrival Job
                          inst_10
                          inst_17
                          j)
                       (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                          Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                          (Prosa_Behavior_Job_JobArrival_job_arrival Job
                             inst_10
                             inst_17
                             j')
                          (Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_task_max_inter_arrival_time
                             Task
                             inst_3
                             inst_6
                             tsk)))))
              Bool_true))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp

Arguments Prosa_Model_Task_Arrival_Task_max_inter_arrival_arr_sep_task_max_inter_arrival 
  Task inst_3
  inst_6 
  Job inst_10
  inst_13
  inst_17 
  arr_seq tsk
```
