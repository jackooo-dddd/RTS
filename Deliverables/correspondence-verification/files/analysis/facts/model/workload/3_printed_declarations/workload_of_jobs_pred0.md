# `workload_of_jobs_pred0`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_pred0`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_pred0`
- Certificate: `workload_of_jobs_pred0_correspondence`

## Official Rocq

```coq
workload_of_jobs_pred0 :
forall {Job : JobType} {H2 : JobCost Job} (jobs : seq (Equality.sort Job)),
@workload_of_jobs Job H2 (pred_of_simpl (@pred0 (Equality.sort Job))) jobs = 0

workload_of_jobs_pred0 is not universe polymorphic
Arguments workload_of_jobs_pred0 {Job H2} jobs%seq_scope
workload_of_jobs_pred0 is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_pred0
Declared in library prosa.analysis.facts.model.workload, line 139, characters 10-32
@workload_of_jobs_pred0
     : forall (Job : JobType) (H2 : JobCost Job) (jobs : seq (Equality.sort Job)),
       @workload_of_jobs Job H2 (pred_of_simpl (@pred0 (Equality.sort Job))) jobs = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_pred0 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (jobs : List Job),
  Prosa.Model.Aggregate.Workload.workload_of_jobs (fun x => false) jobs = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_pred0
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (jobs : List Job),
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6
            (fun _ : Job => Bool_false) jobs)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
