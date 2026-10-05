# `FIFO_is_total`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.fifo.FIFO_is_total`
- Lean: `Prosa.Model.Priority.Fifo.FIFO_is_total`
- Certificate: `FIFO_is_total_correspondence`

## Official Rocq

```coq
FIFO_is_total : forall {Job : JobType} {H : JobArrival Job}, @total_job_priorities Job (@FIFO Job H)

FIFO_is_total is not universe polymorphic
Arguments FIFO_is_total {Job H} x y
FIFO_is_total is opaque
Expands to: Constant prosa.model.priority.fifo.FIFO_is_total
Declared in library prosa.model.priority.fifo, line 29, characters 8-21
@FIFO_is_total
     : forall (Job : JobType) (H : JobArrival Job), @total_job_priorities Job (@FIFO Job H)
```

## Lean

```lean
@Prosa.Model.Priority.Fifo.FIFO_is_total : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Model.Priority.Definitions.total_job_priorities (Prosa.Model.Priority.Fifo.FIFO Job)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Fifo_FIFO_is_total
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3),
       Prosa_Model_Priority_Definitions_total_job_priorities Job
         inst_3
         (Prosa_Model_Priority_Fifo_FIFO Job inst_3
            inst_6)
```
