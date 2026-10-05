# `workload_minus_job_cost'`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_minus_job_cost'`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_minus_job_cost'`
- Certificate: `workload_minus_job_cost'_correspondence`

## Official Rocq

```coq
workload_minus_job_cost' :
forall {Job : JobType} {H2 : JobCost Job} (j : Equality.sort Job) (jobs : seq (Equality.sort Job)),
is_true (@uniq Job jobs) ->
is_true (j \in jobs) ->
forall P : Equality.sort Job -> bool,
@workload_of_jobs Job H2 (fun jhp : Equality.sort Job => P jhp && (jhp != j)) jobs =
@workload_of_jobs Job H2 P jobs - (if P j then @job_cost Job H2 j else 0)

workload_minus_job_cost' is not universe polymorphic
Arguments workload_minus_job_cost' {Job H2} j jobs%seq_scope H_jobs_uniq H_j_in_jobs P%function_scope
workload_minus_job_cost' is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_minus_job_cost'
Declared in library prosa.analysis.facts.model.workload, line 295, characters 8-32
@workload_minus_job_cost'
     : forall (Job : JobType) (H2 : JobCost Job) (j : Equality.sort Job) (jobs : seq (Equality.sort Job)),
       is_true (@uniq Job jobs) ->
       is_true (j \in jobs) ->
       forall P : Equality.sort Job -> bool,
       @workload_of_jobs Job H2 (fun jhp : Equality.sort Job => P jhp && (jhp != j)) jobs =
       @workload_of_jobs Job H2 P jobs - (if P j then @job_cost Job H2 j else 0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_minus_job_cost' : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (j : Job) (jobs : List Job),
  jobs.Nodup →
    decide (j ∈ jobs) = true →
      ∀ (P : Job → Bool),
        Prosa.Model.Aggregate.Workload.workload_of_jobs (fun jhp => P jhp && decide (jhp ≠ j)) jobs =
          Prosa.Model.Aggregate.Workload.workload_of_jobs P jobs - bif P j then Prosa.Behavior.Job.job_cost j else 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_minus_job_cost'
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (j : Job) (jobs : List Job),
       List_Nodup Job jobs ->
       @eq Bool
         (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) jobs j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3) j
               jobs))
         Bool_true ->
       forall P : Job -> Bool,
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6
            (fun jhp : Job =>
             Bool_and (P jhp)
               (Decidable_decide (Ne Job jhp j)
                  (instDecidableNot (@eq Job jhp j)
                     (inst_3 jhp j))))
            jobs)
         (HSub_hSub_inst7 Nat Prosa_Behavior_Job_work Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_3
               inst_6 P jobs)
            (cond Prosa_Behavior_Job_work (P j)
               (Prosa_Behavior_Job_JobCost_job_cost Job
                  inst_3
                  inst_6 j)
               (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))))
```
