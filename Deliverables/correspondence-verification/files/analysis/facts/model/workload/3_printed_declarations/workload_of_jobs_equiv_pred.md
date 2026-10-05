# `workload_of_jobs_equiv_pred`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_equiv_pred`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_equiv_pred`
- Certificate: `workload_of_jobs_equiv_pred_correspondence`

## Official Rocq

```coq
workload_of_jobs_equiv_pred :
forall {Job : JobType} {H2 : JobCost Job} (jobs : seq (Equality.sort Job)) (P P' : pred (Equality.sort Job)),
{in jobs, P =1 P'} -> @workload_of_jobs Job H2 P jobs = @workload_of_jobs Job H2 P' jobs

workload_of_jobs_equiv_pred is not universe polymorphic
Arguments workload_of_jobs_equiv_pred {Job H2} jobs%seq_scope P P' _
workload_of_jobs_equiv_pred is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_equiv_pred
Declared in library prosa.analysis.facts.model.workload, line 163, characters 10-37
@workload_of_jobs_equiv_pred
     : forall (Job : JobType) (H2 : JobCost Job) (jobs : seq (Equality.sort Job))
         (P P' : pred (Equality.sort Job)),
       {in jobs, P =1 P'} -> @workload_of_jobs Job H2 P jobs = @workload_of_jobs Job H2 P' jobs
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_equiv_pred : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (jobs : List Job) (P P' : Job → Bool),
  (∀ (j : Job), decide (j ∈ jobs) = true → P j = P' j) →
    Prosa.Model.Aggregate.Workload.workload_of_jobs P jobs = Prosa.Model.Aggregate.Workload.workload_of_jobs P' jobs
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_equiv_pred
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (jobs : List Job) (P P' : Job -> Bool),
       (forall j : Job,
        @eq Bool
          (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) jobs j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_3)
                (instLawfulBEq Job inst_3)
                j jobs))
          Bool_true ->
        @eq Bool (P j) (P' j)) ->
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P jobs)
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P' jobs)
```
