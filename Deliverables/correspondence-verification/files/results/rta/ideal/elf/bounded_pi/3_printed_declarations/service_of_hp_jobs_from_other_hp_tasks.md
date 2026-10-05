# `service_of_hp_jobs_from_other_hp_tasks`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_hp_tasks`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.service_of_hp_jobs_from_other_hp_tasks`
- Certificate: `service_of_hp_jobs_from_other_hp_tasks_correspondence`

## Official Rocq

```coq
service_of_hp_jobs_from_other_hp_tasks :
forall {Task : TaskType},
PriorityPoint Task ->
forall {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
arrival_sequence Job ->
@schedule Job (ideal.processor_state Job) -> FP_policy Task -> Equality.sort Job -> instant -> instant -> nat

service_of_hp_jobs_from_other_hp_tasks is not universe polymorphic
Arguments service_of_hp_jobs_from_other_hp_tasks {Task H3 Job H4 Arrival} arr_seq sched FP j t1 t2
service_of_hp_jobs_from_other_hp_tasks is transparent
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_hp_tasks
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 377, characters 15-53
@service_of_hp_jobs_from_other_hp_tasks
     : forall Task : TaskType,
       PriorityPoint Task ->
       forall Job : JobType,
       JobTask Job Task ->
       JobArrival Job ->
       arrival_sequence Job ->
       @schedule Job (ideal.processor_state Job) ->
       FP_policy Task -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
service_of_hp_jobs_from_other_hp_tasks =
fun (Task : TaskType) (H3 : PriorityPoint Task) (Job : JobType) (H4 : JobTask Job Task)
  (Arrival : JobArrival Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (ideal.processor_state Job)) (FP : FP_policy Task) (j : Equality.sort Job)
  (t1 t2 : instant) =>
@service_of_jobs Job (ideal.processor_state Job) sched
  ((@hp_task_hep_job Task Job H4 FP (@ELF Task H3 Job Arrival H4 FP))^~ j)
  (@arrivals_between Job arr_seq t1 t2) t1 t2
     : forall {Task : TaskType},
       PriorityPoint Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       arrival_sequence Job ->
       @schedule Job (ideal.processor_state Job) ->
       FP_policy Task -> Equality.sort Job -> instant -> instant -> nat

Arguments service_of_hp_jobs_from_other_hp_tasks {Task H3 Job H4 Arrival} arr_seq sched FP j t1 t2
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.service_of_hp_jobs_from_other_hp_tasks : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
                  Prosa.Model.Priority.Definitions.FP_policy Task →
                    Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Elf.BoundedPi.service_of_hp_jobs_from_other_hp_tasks.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
                  Prosa.Model.Priority.Definitions.FP_policy Task →
                    Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Priority.Gel.PriorityPoint Task]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq sched FP j t1 t2 =>
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched
    (fun jhp => Prosa.Analysis.Definitions.Interference.hp_task_hep_job jhp j)
    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_service_of_hp_jobs_from_other_hp_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7) ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_service_of_hp_jobs_from_other_hp_tasks@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
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
  (inst_17 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_7
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_7))
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_inst4 Job
  inst_7
  (Prosa_Model_Processor_Ideal_processor_state Job
     inst_7)
  sched
  (fun jhp : Job =>
   Prosa_Analysis_Definitions_Interference_hp_task_hep_job Task
     inst_3 Job
     inst_7
     inst_13 FP
     (Prosa_Model_Priority_Elf_ELF Task
        inst_3
        inst_10 Job
        inst_7
        inst_17
        inst_13 FP)
     jhp j)
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_7 arr_seq t1 t2)
  t1 t2
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7) ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Results_Rta_Ideal_Elf_BoundedPi_service_of_hp_jobs_from_other_hp_tasks 
  Task inst_3 
  Job inst_7
  inst_10
  inst_13
  inst_17 arr_seq 
  sched FP j t1 t2
```
