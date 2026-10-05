# `workload_job_and_ahep_eq_workload_hep`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_job_and_ahep_eq_workload_hep`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_job_and_ahep_eq_workload_hep`
- Certificate: `workload_job_and_ahep_eq_workload_hep_correspondence`

## Official Rocq

```coq
workload_job_and_ahep_eq_workload_hep :
forall {Job : JobType} {H2 : JobCost Job} (arr_seq : arrival_sequence Job) {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (j : Equality.sort Job) (t1 t2 : instant),
@workload_of_job Job H2 arr_seq j t1 t2 + @workload_of_other_hep_jobs Job H2 arr_seq JLFP j t1 t2 =
@workload_of_hep_jobs Job H2 arr_seq JLFP j t1 t2

workload_job_and_ahep_eq_workload_hep is not universe polymorphic
Arguments workload_job_and_ahep_eq_workload_hep {Job H2} arr_seq {JLFP} H_priority_is_reflexive j t1 t2
workload_job_and_ahep_eq_workload_hep is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_job_and_ahep_eq_workload_hep
Declared in library prosa.analysis.facts.model.workload, line 218, characters 10-47
@workload_job_and_ahep_eq_workload_hep
     : forall (Job : JobType) (H2 : JobCost Job) (arr_seq : arrival_sequence Job) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       @workload_of_job Job H2 arr_seq j t1 t2 + @workload_of_other_hep_jobs Job H2 arr_seq JLFP j t1 t2 =
       @workload_of_hep_jobs Job H2 arr_seq JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_job_and_ahep_eq_workload_hep : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Model.Aggregate.Workload.workload_of_job arr_seq j t1 t2 +
          Prosa.Model.Aggregate.Workload.workload_of_other_hep_jobs arr_seq j t1 t2 =
        Prosa.Model.Aggregate.Workload.workload_of_hep_jobs arr_seq j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_job_and_ahep_eq_workload_hep
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Nat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_Workload_workload_of_job Job
               inst_3
               inst_6 arr_seq j t1 t2)
            (Prosa_Model_Aggregate_Workload_workload_of_other_hep_jobs Job
               inst_3
               inst_6 arr_seq JLFP j t1 t2))
         (Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job
            inst_3
            inst_6 arr_seq JLFP j t1 t2)
```
