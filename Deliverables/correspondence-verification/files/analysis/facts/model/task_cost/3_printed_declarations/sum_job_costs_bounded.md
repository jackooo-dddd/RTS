# `sum_job_costs_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_cost.sum_job_costs_bounded`
- Lean: `Prosa.Analysis.Facts.Model.TaskCost.sum_job_costs_bounded`
- Certificate: `tc_sum_statement_correspondence`

## Official Rocq

```coq
sum_job_costs_bounded :
forall {Task : concept.TaskType} {H : concept.TaskCost Task} {Job : JobType} {H0 : JobCost Job}
  {H1 : concept.JobTask Job Task} (tsk : Equality.sort Task) (js : seq (Equality.sort Job)),
{in js,
  forall j : Equality.sort Job,
  is_true (@concept.job_of_task Job Task H1 tsk j && @concept.valid_job_cost Task H Job H1 H0 j)} ->
is_true (\sum_(j <- js) @job_cost Job H0 j <= @concept.task_cost Task H tsk * @size (Equality.sort Job) js)

sum_job_costs_bounded is not universe polymorphic
Arguments sum_job_costs_bounded {Task H Job H0 H1} tsk js%seq_scope H_valid_jobs
sum_job_costs_bounded is opaque
Expands to: Constant prosa.analysis.facts.model.task_cost.sum_job_costs_bounded
Declared in library prosa.analysis.facts.model.task_cost, line 49, characters 8-29
@sum_job_costs_bounded
     : forall (Task : concept.TaskType) (H : concept.TaskCost Task) (Job : JobType) 
         (H0 : JobCost Job) (H1 : concept.JobTask Job Task) (tsk : Equality.sort Task)
         (js : seq (Equality.sort Job)),
       {in js,
         forall j : Equality.sort Job,
         is_true (@concept.job_of_task Job Task H1 tsk j && @concept.valid_job_cost Task H Job H1 H0 j)} ->
       is_true
         (\sum_(j <- js) @job_cost Job H0 j <= @concept.task_cost Task H tsk * @size (Equality.sort Job) js)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskCost.sum_job_costs_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Behavior.Job.JobCost Job]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] (tsk : Task) (js : List Job),
  (∀ j ∈ js, (Prosa.Model.Task.Concept.job_of_task tsk j && Prosa.Model.Task.Concept.valid_job_cost j) = true) →
    (List.map Prosa.Behavior.Job.job_cost js).sum ≤ Prosa.Model.Task.Concept.task_cost tsk * js.length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskCost_sum_job_costs_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (tsk : Task) (js : List Job),
       (forall j : Job,
        Membership_mem Job (List Job) (List_instMembership Job) js j ->
        @eq Bool
          (Bool_and
             (Prosa_Model_Task_Concept_job_of_task Job
                inst_10 Task
                inst_3
                inst_16 tsk j)
             (Prosa_Model_Task_Concept_valid_job_cost Task
                inst_3
                inst_6 Job
                inst_10
                inst_16
                inst_13 j))
          Bool_true) ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (List_sum_inst1 Prosa_Behavior_Job_work instAddNat
            (MulZeroClass_toZero_inst1 Prosa_Behavior_Job_work Nat_instMulZeroClass)
            (List_map_inst2 Job Prosa_Behavior_Job_work
               (Prosa_Behavior_Job_JobCost_job_cost Job
                  inst_10
                  inst_13)
               js))
         (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_6 tsk)
            (List_length Job js))
```
