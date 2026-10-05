# `workload_of_jobs_le_sum_over_partitions`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_le_sum_over_partitions`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_le_sum_over_partitions`
- Certificate: `workload_of_jobs_le_sum_over_partitions_correspondence`

## Official Rocq

```coq
workload_of_jobs_le_sum_over_partitions :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H2 : JobCost Job}
  {P : pred (Equality.sort Job)} (Q : pred (Equality.sort Task)) {js : seq (Equality.sort Job)}
  (ts : seq (Equality.sort Task)),
{in js, forall j : Equality.sort Job, is_true (@job_task Job Task H0 j \in ts)} ->
{in js, forall j : Equality.sort Job, is_true (P j) -> is_true (Q (@job_task Job Task H0 j))} ->
is_true
  (let P_and_job_of :=
     fun (tsk_o : Equality.sort Task) (j : Equality.sort Job) => P j && (@job_task Job Task H0 j == tsk_o) in
   @workload_of_jobs Job H2 P js <=
   \sum_(tsk_o <- ts | Q tsk_o) @workload_of_jobs Job H2 (P_and_job_of tsk_o) js)

workload_of_jobs_le_sum_over_partitions is not universe polymorphic
Arguments workload_of_jobs_le_sum_over_partitions {Task Job H0 H2 P} Q {js}%seq_scope ts%seq_scope _ _
workload_of_jobs_le_sum_over_partitions is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_le_sum_over_partitions
Declared in library prosa.analysis.facts.model.workload, line 55, characters 8-47
@workload_of_jobs_le_sum_over_partitions
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H2 : JobCost Job)
         (P : pred (Equality.sort Job)) (Q : pred (Equality.sort Task)) (js : seq (Equality.sort Job))
         (ts : seq (Equality.sort Task)),
       {in js, forall j : Equality.sort Job, is_true (@job_task Job Task H0 j \in ts)} ->
       {in js, forall j : Equality.sort Job, is_true (P j) -> is_true (Q (@job_task Job Task H0 j))} ->
       is_true
         (let P_and_job_of :=
            fun (tsk_o : Equality.sort Task) (j : Equality.sort Job) =>
            P j && (@job_task Job Task H0 j == tsk_o) in
          @workload_of_jobs Job H2 P js <=
          \sum_(tsk_o <- ts | Q tsk_o) @workload_of_jobs Job H2 (P_and_job_of tsk_o) js)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_le_sum_over_partitions : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobCost Job] (P : Job → Bool) (Q : Task → Bool) (js : List Job) (ts : List Task),
  (∀ (j : Job), decide (j ∈ js) = true → decide (Prosa.Model.Task.Concept.job_task j ∈ ts) = true) →
    (∀ (j : Job), decide (j ∈ js) = true → P j = true → Q (Prosa.Model.Task.Concept.job_task j) = true) →
      have P_and_job_of := fun tsk_o j => P j && decide (Prosa.Model.Task.Concept.job_task j = tsk_o);
      Prosa.Model.Aggregate.Workload.workload_of_jobs P js ≤
        Prosa.Util.Sum.sumFiltered ts Q fun tsk_o =>
          Prosa.Model.Aggregate.Workload.workload_of_jobs (P_and_job_of tsk_o) js
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_le_sum_over_partitions
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (P : Job -> Bool) (Q : Task -> Bool) (js : List Job) (ts : List Task),
       (forall j : Job,
        @eq Bool
          (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) js j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_7)
                (instLawfulBEq Job inst_7)
                j js))
          Bool_true ->
        @eq Bool
          (Decidable_decide
             (Membership_mem Task (List Task) (List_instMembership Task) ts
                (Prosa_Model_Task_Concept_JobTask_job_task Job
                   inst_7 Task
                   inst_3
                   inst_10 j))
             (List_instDecidableMemOfLawfulBEq Task
                (instBEqOfDecidableEq Task
                   inst_3)
                (instLawfulBEq Task inst_3)
                (Prosa_Model_Task_Concept_JobTask_job_task Job
                   inst_7 Task
                   inst_3
                   inst_10 j)
                ts))
          Bool_true) ->
       (forall j : Job,
        @eq Bool
          (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) js j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_7)
                (instLawfulBEq Job inst_7)
                j js))
          Bool_true ->
        @eq Bool (P j) Bool_true ->
        @eq Bool
          (Q
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_10 j))
          Bool_true) ->
       let P_and_job_of :=
         fun (tsk_o : Task) (j : Job) =>
         Bool_and (P j)
           (Decidable_decide
              (@eq Task
                 (Prosa_Model_Task_Concept_JobTask_job_task Job
                    inst_7 Task
                    inst_3
                    inst_10 j)
                 tsk_o)
              (inst_3
                 (Prosa_Model_Task_Concept_JobTask_job_task Job
                    inst_7 Task
                    inst_3
                    inst_10 j)
                 tsk_o))
         in
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_14 P js)
         (Prosa_Util_Sum_sumFiltered Task ts Q
            (fun tsk_o : Task =>
             Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_7
               inst_14 
               (P_and_job_of tsk_o) js))
```
