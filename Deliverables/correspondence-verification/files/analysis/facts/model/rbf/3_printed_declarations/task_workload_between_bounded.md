# `task_workload_between_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.task_workload_between_bounded`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.task_workload_between_bounded`
- Certificate: `task_workload_between_bounded_correspondence`

## Official Rocq

```coq
task_workload_between_bounded :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H1 : JobTask Job Task} 
  {H3 : JobCost Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall (tsk : Equality.sort Task) (t1 t2 : instant),
is_true
  (@task_workload_between Task Job H1 H3 arr_seq tsk t1 t2 <=
   @task_cost Task H tsk * @number_of_task_arrivals Job Task H1 arr_seq tsk t1 t2)

task_workload_between_bounded is not universe polymorphic
Arguments task_workload_between_bounded {Task H Job H1 H3} arr_seq H_valid_job_cost tsk t1 t2
task_workload_between_bounded is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.task_workload_between_bounded
Declared in library prosa.analysis.facts.model.rbf, line 49, characters 10-39
@task_workload_between_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H1 : JobTask Job Task)
         (H3 : JobCost Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall (tsk : Equality.sort Task) (t1 t2 : instant),
       is_true
         (@task_workload_between Task Job H1 H3 arr_seq tsk t1 t2 <=
          @task_cost Task H tsk * @number_of_task_arrivals Job Task H1 arr_seq tsk t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.task_workload_between_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Model.Aggregate.Workload.task_workload_between arr_seq tsk t1 t2 ≤
        Prosa.Model.Task.Concept.task_cost tsk * Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_task_workload_between_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_10
                                                                                Task
                                                                                inst_3)
         (inst_17 : Prosa_Behavior_Job_JobCost
                                                                                Job
                                                                                inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq ->
       forall (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_task_workload_between Task
            inst_3 Job
            inst_10
            inst_13
            inst_17 arr_seq tsk t1 t2)
         (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_6 tsk)
            (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
               inst_10 Task
               inst_3
               inst_13 arr_seq tsk t1 t2))
```
