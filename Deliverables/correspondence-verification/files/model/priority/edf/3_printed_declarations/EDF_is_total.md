# `EDF_is_total`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.edf.EDF_is_total`
- Lean: `Prosa.Model.Priority.Edf.EDF_is_total`
- Certificate: `EDF_is_total_correspondence`

## Official Rocq

```coq
EDF_is_total : forall {Job : JobType} {H : JobDeadline Job}, @total_job_priorities Job (@EDF Job H)

EDF_is_total is not universe polymorphic
Arguments EDF_is_total {Job H} x y
EDF_is_total is opaque
Expands to: Constant prosa.model.priority.edf.EDF_is_total
Declared in library prosa.model.priority.edf, line 33, characters 8-20
@EDF_is_total
     : forall (Job : JobType) (H : JobDeadline Job), @total_job_priorities Job (@EDF Job H)
```

## Lean

```lean
@Prosa.Model.Priority.Edf.EDF_is_total : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobDeadline Job],
  Prosa.Model.Priority.Definitions.total_job_priorities (Prosa.Model.Priority.Edf.EDF Job)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Edf_EDF_is_total
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                           inst_3),
       Prosa_Model_Priority_Definitions_total_job_priorities Job
         inst_3
         (Prosa_Model_Priority_Edf_EDF Job inst_3
            inst_6)
```
