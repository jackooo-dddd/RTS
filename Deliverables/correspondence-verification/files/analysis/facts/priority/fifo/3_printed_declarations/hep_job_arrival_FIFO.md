# `hep_job_arrival_FIFO`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.fifo.hep_job_arrival_FIFO`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.hep_job_arrival_FIFO`
- Certificate: `hep_job_arrival_FIFO_correspondence`

## Official Rocq

```coq
hep_job_arrival_FIFO :
forall {Job : JobType} {Arrival : JobArrival Job} (j j' : Equality.sort Job),
@hep_job Job (@FIFO Job Arrival) j j' = (@job_arrival Job Arrival j <= @job_arrival Job Arrival j')

hep_job_arrival_FIFO is not universe polymorphic
Arguments hep_job_arrival_FIFO {Job Arrival} j j'
hep_job_arrival_FIFO is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.hep_job_arrival_FIFO
Declared in library prosa.analysis.facts.priority.fifo, line 23, characters 7-27
@hep_job_arrival_FIFO
     : forall (Job : JobType) (Arrival : JobArrival Job) (j j' : Equality.sort Job),
       @hep_job Job (@FIFO Job Arrival) j j' = (@job_arrival Job Arrival j <= @job_arrival Job Arrival j')
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.hep_job_arrival_FIFO : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] (j j' : Job),
  Prosa.Model.Priority.Definitions.hep_job j j' =
    decide (Prosa.Behavior.Job.job_arrival j ≤ Prosa.Behavior.Job.job_arrival j')
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_hep_job_arrival_FIFO
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (j j' : Job),
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_3
               inst_6)
            j j')
         (Decidable_decide
            (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_6 j)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_6 j'))
            (Nat_decLe
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_6 j)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_6 j')))
```
