# `workload_of_jobs0`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs0`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs0`
- Certificate: `workload_of_jobs0_correspondence`

## Official Rocq

```coq
workload_of_jobs0 :
forall {Job : JobType} {H2 : JobCost Job} (P : pred (Equality.sort Job)), @workload_of_jobs Job H2 P [::] = 0

workload_of_jobs0 is not universe polymorphic
Arguments workload_of_jobs0 {Job H2} P
workload_of_jobs0 is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs0
Declared in library prosa.analysis.facts.model.workload, line 50, characters 8-25
@workload_of_jobs0
     : forall (Job : JobType) (H2 : JobCost Job) (P : pred (Equality.sort Job)),
       @workload_of_jobs Job H2 P [::] = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs0 : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobCost Job] (P : Job → Bool), Prosa.Model.Aggregate.Workload.workload_of_jobs P [] = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs0
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (P : Job -> Bool),
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P 
            (List_nil Job))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
