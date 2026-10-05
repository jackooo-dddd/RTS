# `FIFO_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.fifo.FIFO_is_transitive`
- Lean: `Prosa.Model.Priority.Fifo.FIFO_is_transitive`
- Certificate: `FIFO_is_transitive_correspondence`

## Official Rocq

```coq
FIFO_is_transitive :
forall {Job : JobType} {H : JobArrival Job}, @transitive_job_priorities Job (@FIFO Job H)

FIFO_is_transitive is not universe polymorphic
Arguments FIFO_is_transitive {Job H} y x z _ _
FIFO_is_transitive is opaque
Expands to: Constant prosa.model.priority.fifo.FIFO_is_transitive
Declared in library prosa.model.priority.fifo, line 25, characters 8-26
@FIFO_is_transitive
     : forall (Job : JobType) (H : JobArrival Job), @transitive_job_priorities Job (@FIFO Job H)
```

## Lean

```lean
@Prosa.Model.Priority.Fifo.FIFO_is_transitive : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Model.Priority.Definitions.transitive_job_priorities (Prosa.Model.Priority.Fifo.FIFO Job)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Fifo_FIFO_is_transitive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3),
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3
         (Prosa_Model_Priority_Fifo_FIFO Job inst_3
            inst_6)
```
