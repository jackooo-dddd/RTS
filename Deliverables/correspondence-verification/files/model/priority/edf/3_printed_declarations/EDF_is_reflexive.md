# `EDF_is_reflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.edf.EDF_is_reflexive`
- Lean: `Prosa.Model.Priority.Edf.EDF_is_reflexive`
- Certificate: `EDF_is_reflexive_correspondence`

## Official Rocq

```coq
EDF_is_reflexive : forall {Job : JobType} {H : JobDeadline Job}, @reflexive_job_priorities Job (@EDF Job H)

EDF_is_reflexive is not universe polymorphic
Arguments EDF_is_reflexive {Job H} x
EDF_is_reflexive is opaque
Expands to: Constant prosa.model.priority.edf.EDF_is_reflexive
Declared in library prosa.model.priority.edf, line 25, characters 8-24
@EDF_is_reflexive
     : forall (Job : JobType) (H : JobDeadline Job), @reflexive_job_priorities Job (@EDF Job H)
```

## Lean

```lean
@Prosa.Model.Priority.Edf.EDF_is_reflexive : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobDeadline Job],
  Prosa.Model.Priority.Definitions.reflexive_job_priorities (Prosa.Model.Priority.Edf.EDF Job)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Edf_EDF_is_reflexive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                            inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3
         (Prosa_Model_Priority_Edf_EDF Job inst_3
            inst_6)
```
