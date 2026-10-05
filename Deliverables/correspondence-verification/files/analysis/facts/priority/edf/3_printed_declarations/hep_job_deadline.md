# `hep_job_deadline`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.edf.hep_job_deadline`
- Lean: `Prosa.Analysis.Facts.Priority.Edf.hep_job_deadline`
- Certificate: `hep_job_deadline_correspondence`

## Official Rocq

```coq
hep_job_deadline :
forall {Job : JobType} {H0 : JobDeadline Job} (j j' : Equality.sort Job),
@hep_job Job (@EDF Job H0) j j' = (@job_deadline Job H0 j <= @job_deadline Job H0 j')

hep_job_deadline is not universe polymorphic
Arguments hep_job_deadline {Job H0} j j'
hep_job_deadline is opaque
Expands to: Constant prosa.analysis.facts.priority.edf.hep_job_deadline
Declared in library prosa.analysis.facts.priority.edf, line 18, characters 9-25
@hep_job_deadline
     : forall (Job : JobType) (H0 : JobDeadline Job) (j j' : Equality.sort Job),
       @hep_job Job (@EDF Job H0) j j' = (@job_deadline Job H0 j <= @job_deadline Job H0 j')
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Edf.hep_job_deadline : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobDeadline Job] (j j' : Job),
  Prosa.Model.Priority.Definitions.hep_job j j' =
    decide (Prosa.Behavior.Job.job_deadline j ≤ Prosa.Behavior.Job.job_deadline j')
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Edf_hep_job_deadline
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (j j' : Job),
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3
            (Prosa_Model_Priority_Edf_EDF Job
               inst_3
               inst_6)
            j j')
         (Decidable_decide
            (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
               (Prosa_Behavior_Job_JobDeadline_job_deadline Job
                  inst_3
                  inst_6 j)
               (Prosa_Behavior_Job_JobDeadline_job_deadline Job
                  inst_3
                  inst_6 j'))
            (Nat_decLe
               (Prosa_Behavior_Job_JobDeadline_job_deadline Job
                  inst_3
                  inst_6 j)
               (Prosa_Behavior_Job_JobDeadline_job_deadline Job
                  inst_3
                  inst_6 j')))
```
