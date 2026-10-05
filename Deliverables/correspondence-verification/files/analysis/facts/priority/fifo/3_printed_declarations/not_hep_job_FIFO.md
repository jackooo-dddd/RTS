# `not_hep_job_FIFO`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.fifo.not_hep_job_FIFO`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.not_hep_job_FIFO`
- Certificate: `not_hep_job_FIFO_correspondence`

## Official Rocq

```coq
not_hep_job_FIFO :
forall {Job : JobType} {Arrival : JobArrival Job} (j j' : Equality.sort Job),
is_true (~~ @hep_job Job (@FIFO Job Arrival) j j') -> is_true (@hep_job Job (@FIFO Job Arrival) j' j)

not_hep_job_FIFO is not universe polymorphic
Arguments not_hep_job_FIFO {Job Arrival} j j' _
not_hep_job_FIFO is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.not_hep_job_FIFO
Declared in library prosa.analysis.facts.priority.fifo, line 39, characters 7-23
@not_hep_job_FIFO
     : forall (Job : JobType) (Arrival : JobArrival Job) (j j' : Equality.sort Job),
       is_true (~~ @hep_job Job (@FIFO Job Arrival) j j') -> is_true (@hep_job Job (@FIFO Job Arrival) j' j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.not_hep_job_FIFO : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] (j j' : Job),
  (!Prosa.Model.Priority.Definitions.hep_job j j') = true → Prosa.Model.Priority.Definitions.hep_job j' j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_not_hep_job_FIFO
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (j j' : Job),
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3
               (Prosa_Model_Priority_Fifo_FIFO Job
                  inst_3
                  inst_6)
               j j'))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_3
               inst_6)
            j' j)
         Bool_true
```
