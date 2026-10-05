# `FIFO_is_reflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.fifo.FIFO_is_reflexive`
- Lean: `Prosa.Model.Priority.Fifo.FIFO_is_reflexive`
- Certificate: `FIFO_is_reflexive_correspondence`

## Official Rocq

```coq
FIFO_is_reflexive : forall {Job : JobType} {H : JobArrival Job}, @reflexive_job_priorities Job (@FIFO Job H)

FIFO_is_reflexive is not universe polymorphic
Arguments FIFO_is_reflexive {Job H} x
FIFO_is_reflexive is opaque
Expands to: Constant prosa.model.priority.fifo.FIFO_is_reflexive
Declared in library prosa.model.priority.fifo, line 21, characters 8-25
@FIFO_is_reflexive
     : forall (Job : JobType) (H : JobArrival Job), @reflexive_job_priorities Job (@FIFO Job H)
```

## Lean

```lean
@Prosa.Model.Priority.Fifo.FIFO_is_reflexive : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Model.Priority.Definitions.reflexive_job_priorities (Prosa.Model.Priority.Fifo.FIFO Job)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Fifo_FIFO_is_reflexive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3
         (Prosa_Model_Priority_Fifo_FIFO Job inst_3
            inst_6)
```
