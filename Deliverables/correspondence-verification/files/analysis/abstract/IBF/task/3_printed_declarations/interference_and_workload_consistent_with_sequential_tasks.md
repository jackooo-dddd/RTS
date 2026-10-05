# `interference_and_workload_consistent_with_sequential_tasks`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.IBF.task.interference_and_workload_consistent_with_sequential_tasks`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks`
- Certificate: `interference_and_workload_consistent_with_sequential_tasks_correspondence`

## Official Rocq

```coq
interference_and_workload_consistent_with_sequential_tasks :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> Equality.sort Task -> Interference Job -> InterferingWorkload Job -> Prop

interference_and_workload_consistent_with_sequential_tasks is not universe polymorphic
Arguments interference_and_workload_consistent_with_sequential_tasks {Task Job H0 H1 jc PState} 
  arr_seq sched tsk {H3 H4}
interference_and_workload_consistent_with_sequential_tasks is transparent
Expands to: Constant
            prosa.analysis.abstract.IBF.task.interference_and_workload_consistent_with_sequential_tasks
Declared in library prosa.analysis.abstract.IBF.task, line 169, characters 13-71
@interference_and_workload_consistent_with_sequential_tasks
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> Equality.sort Task -> Interference Job -> InterferingWorkload Job -> Prop
```

Body:

```coq
interference_and_workload_consistent_with_sequential_tasks =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job) 
  (jc : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (H3 : Interference Job)
  (H4 : InterferingWorkload Job) =>
forall (j : Equality.sort Job) (t1 t2 : instant),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (0 < @job_cost Job jc j) ->
@busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
@task_workload_between Task Job H0 jc arr_seq tsk 0 t1 =
@task_service_of_jobs_in Task Job H0 PState sched tsk (@arrivals_between Job arr_seq 0 t1) 0 t1
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> Equality.sort Task -> Interference Job -> InterferingWorkload Job -> Prop

Arguments interference_and_workload_consistent_with_sequential_tasks {Task Job H0 H1 jc PState} 
  arr_seq sched tsk {H3 H4}
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    Task →
                      [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                        [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] → Prop
```

Body:

```lean
def Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks.{u_1, u_2, u_3, u_4} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    Task →
                      [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                        [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] → Prop :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched tsk
    [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] =>
  ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Behavior.Job.job_cost j > 0 →
          Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
            Prosa.Model.Aggregate.Workload.task_workload_between arr_seq tsk 0 t1 =
              Prosa.Model.Aggregate.ServiceOfJobs.task_service_of_jobs_in sched tsk
                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 t1) 0 t1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks@{u_1 u_2 u_3 u_4
Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_3+2_u_4+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0
Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
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
  (tsk : Task)
  (inst_27 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                              Job
                                                                              inst_3)
  (inst_30 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                              Job
                                                                              inst_3) =>
forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_3 Task
     inst_7
     inst_10 tsk j)
  Bool_true ->
GT_gt_inst1 Prosa_Behavior_Job_work instLTNat
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_17 j)
  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)) ->
Prosa_Analysis_Abstract_Definitions_busy_interval Job
  inst_3
  inst_27
  inst_30
  inst_14
  inst_17 PState sched j t1 t2 ->
@eq Nat
  (Prosa_Model_Aggregate_Workload_task_workload_between Task
     inst_7 Job
     inst_3
     inst_10
     inst_17 arr_seq tsk
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t1)
  (Prosa_Model_Aggregate_ServiceOfJobs_task_service_of_jobs_in Task
     inst_7 Job
     inst_3
     inst_10 PState sched tsk
     (Prosa_Behavior_Arrival_sequence_arrivals_between Job
        inst_3 arr_seq
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t1)
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t1)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       SProp

Arguments Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks 
  Job inst_3 Task
  inst_7
  inst_10
  inst_14
  inst_17 PState arr_seq 
  sched tsk inst_27
  inst_30
```
