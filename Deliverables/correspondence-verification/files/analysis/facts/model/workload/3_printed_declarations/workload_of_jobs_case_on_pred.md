# `workload_of_jobs_case_on_pred`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_case_on_pred`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_case_on_pred`
- Certificate: `workload_of_jobs_case_on_pred_correspondence`

## Official Rocq

```coq
workload_of_jobs_case_on_pred :
forall {Job : JobType} {H2 : JobCost Job} (jobs : seq (Equality.sort Job)) (P P' : pred (Equality.sort Job)),
@workload_of_jobs Job H2 P jobs =
@workload_of_jobs Job H2 (fun j : Equality.sort Job => P j && P' j) jobs +
@workload_of_jobs Job H2 (fun j : Equality.sort Job => P j && ~~ P' j) jobs

workload_of_jobs_case_on_pred is not universe polymorphic
Arguments workload_of_jobs_case_on_pred {Job H2} jobs%seq_scope P P'
workload_of_jobs_case_on_pred is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_case_on_pred
Declared in library prosa.analysis.facts.model.workload, line 149, characters 10-39
@workload_of_jobs_case_on_pred
     : forall (Job : JobType) (H2 : JobCost Job) (jobs : seq (Equality.sort Job))
         (P P' : pred (Equality.sort Job)),
       @workload_of_jobs Job H2 P jobs =
       @workload_of_jobs Job H2 (fun j : Equality.sort Job => P j && P' j) jobs +
       @workload_of_jobs Job H2 (fun j : Equality.sort Job => P j && ~~ P' j) jobs
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_case_on_pred : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (jobs : List Job) (P P' : Job → Bool),
  Prosa.Model.Aggregate.Workload.workload_of_jobs P jobs =
    Prosa.Model.Aggregate.Workload.workload_of_jobs (fun j => P j && P' j) jobs +
      Prosa.Model.Aggregate.Workload.workload_of_jobs (fun j => P j && !P' j) jobs
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_case_on_pred
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (jobs : List Job) (P P' : Job -> Bool),
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P jobs)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_3
               inst_6
               (fun j : Job => Bool_and (P j) (P' j)) jobs)
            (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_3
               inst_6
               (fun j : Job => Bool_and (P j) (Bool_not (P' j))) jobs))
```
