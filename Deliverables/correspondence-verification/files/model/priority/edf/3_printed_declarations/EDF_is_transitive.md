# `EDF_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.edf.EDF_is_transitive`
- Lean: `Prosa.Model.Priority.Edf.EDF_is_transitive`
- Certificate: `EDF_is_transitive_correspondence`

## Official Rocq

```coq
EDF_is_transitive : forall {Job : JobType} {H : JobDeadline Job}, @transitive_job_priorities Job (@EDF Job H)

EDF_is_transitive is not universe polymorphic
Arguments EDF_is_transitive {Job H} y x z _ _
EDF_is_transitive is opaque
Expands to: Constant prosa.model.priority.edf.EDF_is_transitive
Declared in library prosa.model.priority.edf, line 29, characters 8-25
@EDF_is_transitive
     : forall (Job : JobType) (H : JobDeadline Job), @transitive_job_priorities Job (@EDF Job H)
```

## Lean

```lean
@Prosa.Model.Priority.Edf.EDF_is_transitive : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobDeadline Job],
  Prosa.Model.Priority.Definitions.transitive_job_priorities (Prosa.Model.Priority.Edf.EDF Job)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Edf_EDF_is_transitive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                           inst_3),
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3
         (Prosa_Model_Priority_Edf_EDF Job inst_3
            inst_6)
```
