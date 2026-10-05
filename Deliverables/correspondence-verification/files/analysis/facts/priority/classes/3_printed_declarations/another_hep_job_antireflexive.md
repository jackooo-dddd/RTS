# `another_hep_job_antireflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.another_hep_job_antireflexive`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.another_hep_job_antireflexive`
- Certificate: `another_hep_job_antireflexive_correspondence`

## Official Rocq

```coq
another_hep_job_antireflexive :
forall {Job : JobType} {H0 : JLFP_policy Job} (j : Equality.sort Job),
~ is_true (@another_hep_job Job H0 j j)

another_hep_job_antireflexive is not universe polymorphic
Arguments another_hep_job_antireflexive {Job H0} j _
another_hep_job_antireflexive is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.another_hep_job_antireflexive
Declared in library prosa.analysis.facts.priority.classes, line 19, characters 8-37
@another_hep_job_antireflexive
     : forall (Job : JobType) (H0 : JLFP_policy Job) (j : Equality.sort Job),
       ~ is_true (@another_hep_job Job H0 j j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.another_hep_job_antireflexive : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j : Job),
  ¬Prosa.Model.Priority.Definitions.another_hep_job j j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_another_hep_job_antireflexive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
         (j : Job),
       Not
         (@eq Bool
            (Prosa_Model_Priority_Definitions_another_hep_job Job
               inst_3
               inst_6 j j)
            Bool_true)
```
