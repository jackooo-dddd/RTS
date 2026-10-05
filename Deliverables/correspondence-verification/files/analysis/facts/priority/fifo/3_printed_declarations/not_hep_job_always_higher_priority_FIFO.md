# `not_hep_job_always_higher_priority_FIFO`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.fifo.not_hep_job_always_higher_priority_FIFO`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.not_hep_job_always_higher_priority_FIFO`
- Certificate: `not_hep_job_always_higher_priority_FIFO_correspondence`

## Official Rocq

```coq
not_hep_job_always_higher_priority_FIFO :
forall {Job : JobType} {Arrival : JobArrival Job} (j j' : Equality.sort Job),
is_true (~~ @hep_job Job (@FIFO Job Arrival) j j') ->
@always_higher_priority Job (@JLFP_to_JLDP Job (@FIFO Job Arrival)) j' j

not_hep_job_always_higher_priority_FIFO is not universe polymorphic
Arguments not_hep_job_always_higher_priority_FIFO {Job Arrival} j j' _ t
not_hep_job_always_higher_priority_FIFO is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.not_hep_job_always_higher_priority_FIFO
Declared in library prosa.analysis.facts.priority.fifo, line 48, characters 7-46
@not_hep_job_always_higher_priority_FIFO
     : forall (Job : JobType) (Arrival : JobArrival Job) (j j' : Equality.sort Job),
       is_true (~~ @hep_job Job (@FIFO Job Arrival) j j') ->
       @always_higher_priority Job (@JLFP_to_JLDP Job (@FIFO Job Arrival)) j' j
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.not_hep_job_always_higher_priority_FIFO : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] (j j' : Job),
  (!Prosa.Model.Priority.Definitions.hep_job j j') = true →
    Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority j' j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_not_hep_job_always_higher_priority_FIFO
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
       Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority Job
         inst_3
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_3
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_3
               inst_6))
         j' j
```
