# `workload_of_jobs_weaken`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_weaken`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_weaken`
- Certificate: `workload_of_jobs_weaken_correspondence`

## Official Rocq

```coq
workload_of_jobs_weaken :
forall {Job : JobType} {H2 : JobCost Job} (P1 P2 : pred (Equality.sort Job)) (jobs : seq (Equality.sort Job)),
(forall j : Equality.sort Job, is_true (P1 j) -> is_true (P2 j)) ->
is_true (@workload_of_jobs Job H2 P1 jobs <= @workload_of_jobs Job H2 P2 jobs)

workload_of_jobs_weaken is not universe polymorphic
Arguments workload_of_jobs_weaken {Job H2} P1 P2 jobs%seq_scope _%function_scope
workload_of_jobs_weaken is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_weaken
Declared in library prosa.analysis.facts.model.workload, line 39, characters 8-31
@workload_of_jobs_weaken
     : forall (Job : JobType) (H2 : JobCost Job) (P1 P2 : pred (Equality.sort Job))
         (jobs : seq (Equality.sort Job)),
       (forall j : Equality.sort Job, is_true (P1 j) -> is_true (P2 j)) ->
       is_true (@workload_of_jobs Job H2 P1 jobs <= @workload_of_jobs Job H2 P2 jobs)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_weaken : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (P1 P2 : Job → Bool) (jobs : List Job),
  (∀ (j : Job), P1 j = true → P2 j = true) →
    Prosa.Model.Aggregate.Workload.workload_of_jobs P1 jobs ≤ Prosa.Model.Aggregate.Workload.workload_of_jobs P2 jobs
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_weaken
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (P1 P2 : Job -> Bool) (jobs : List Job),
       (forall j : Job, @eq Bool (P1 j) Bool_true -> @eq Bool (P2 j) Bool_true) ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P1 jobs)
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P2 jobs)
```
