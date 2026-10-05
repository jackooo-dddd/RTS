# `workload_of_other_jobs_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_other_jobs_split`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_other_jobs_split`
- Certificate: `workload_of_other_jobs_split_correspondence`

## Official Rocq

```coq
workload_of_other_jobs_split :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H2 : JobCost Job} 
  {H3 : JLFP_policy Job} (jobs : seq (Equality.sort Job)) (j : Equality.sort Job),
@workload_of_jobs Job H2 ((@another_hep_job Job H3)^~ j) jobs =
@workload_of_jobs Job H2 ((@another_task_hep_job Task Job H0 H3)^~ j) jobs +
@workload_of_jobs Job H2 ((@another_hep_job_of_same_task Task Job H0 H3)^~ j) jobs

workload_of_other_jobs_split is not universe polymorphic
Arguments workload_of_other_jobs_split {Task Job H0 H2 H3} jobs%seq_scope j
workload_of_other_jobs_split is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_other_jobs_split
Declared in library prosa.analysis.facts.model.workload, line 100, characters 10-38
@workload_of_other_jobs_split
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H2 : JobCost Job)
         (H3 : JLFP_policy Job) (jobs : seq (Equality.sort Job)) (j : Equality.sort Job),
       @workload_of_jobs Job H2 ((@another_hep_job Job H3)^~ j) jobs =
       @workload_of_jobs Job H2 ((@another_task_hep_job Task Job H0 H3)^~ j) jobs +
       @workload_of_jobs Job H2 ((@another_hep_job_of_same_task Task Job H0 H3)^~ j) jobs
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_other_jobs_split : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobCost Job]
  [inst_4 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (jobs : List Job) (j : Job),
  Prosa.Model.Aggregate.Workload.workload_of_jobs (fun x => Prosa.Model.Priority.Definitions.another_hep_job x j) jobs =
    Prosa.Model.Aggregate.Workload.workload_of_jobs (fun x => Prosa.Model.Priority.Definitions.another_task_hep_job x j)
        jobs +
      Prosa.Model.Aggregate.Workload.workload_of_jobs
        (fun x => Prosa.Model.Priority.Definitions.another_hep_job_of_same_task x j) jobs
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_other_jobs_split
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
         (inst_17 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (jobs : List Job) (j : Job),
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_14
            (fun x : Job =>
             Prosa_Model_Priority_Definitions_another_hep_job Job
               inst_7
               inst_17 x j)
            jobs)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_7
               inst_14
               (fun x : Job =>
                Prosa_Model_Priority_Definitions_another_task_hep_job Task
                  inst_3 Job
                  inst_7
                  inst_10
                  inst_17 x j)
               jobs)
            (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_7
               inst_14
               (fun x : Job =>
                Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task
                  inst_3 Job
                  inst_7
                  inst_10
                  inst_17 x j)
               jobs))
```
