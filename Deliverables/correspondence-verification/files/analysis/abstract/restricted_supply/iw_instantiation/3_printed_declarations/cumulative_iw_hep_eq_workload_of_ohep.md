# `cumulative_iw_hep_eq_workload_of_ohep`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_iw_hep_eq_workload_of_ohep`
- Certificate: `cumulative_iw_hep_eq_workload_of_ohep_correspondence`

## Official Rocq

```coq
cumulative_iw_hep_eq_workload_of_ohep :
forall {Job : JobType} {H2 : JobCost Job} (arr_seq : arrival_sequence Job) {JLFP : JLFP_policy Job}
  (t1 t2 : instant) (j : Equality.sort Job),
@cumulative_other_hep_jobs_interfering_workload Job H2 arr_seq JLFP j t1 t2 =
@workload_of_other_hep_jobs Job H2 arr_seq JLFP j t1 t2

cumulative_iw_hep_eq_workload_of_ohep is not universe polymorphic
Arguments cumulative_iw_hep_eq_workload_of_ohep {Job H2} arr_seq {JLFP} t1 t2 j
cumulative_iw_hep_eq_workload_of_ohep is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep
Declared in library prosa.analysis.abstract.restricted_supply.iw_instantiation, line 231, characters 10-47
@cumulative_iw_hep_eq_workload_of_ohep
     : forall (Job : JobType) (H2 : JobCost Job) (arr_seq : arrival_sequence Job) 
         (JLFP : JLFP_policy Job) (t1 t2 : instant) (j : Equality.sort Job),
       @cumulative_other_hep_jobs_interfering_workload Job H2 arr_seq JLFP j t1 t2 =
       @workload_of_other_hep_jobs Job H2 arr_seq JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_iw_hep_eq_workload_of_ohep : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [inst_2 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  Prosa.Analysis.Definitions.Interference.cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2 =
    Prosa.Model.Aggregate.Workload.workload_of_other_hep_jobs arr_seq j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_cumulative_iw_hep_eq_workload_of_ohep
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (inst_15 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (t1 t2 : Prosa_Behavior_Time_instant) (j : Job),
       @eq Nat
         (Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload Job
            inst_7
            inst_10
            arr_seq
            inst_15 j
            t1 t2)
         (Prosa_Model_Aggregate_Workload_workload_of_other_hep_jobs Job
            inst_7
            inst_10
            arr_seq
            inst_15 j
            t1 t2)
```
