# `hep_job_arrival_gel`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.gel.hep_job_arrival_gel`
- Lean: `Prosa.Analysis.Facts.Priority.Gel.hep_job_arrival_gel`
- Certificate: `hep_job_arrival_gel_correspondence`

## Official Rocq

```coq
hep_job_arrival_gel :
forall {Task : concept.TaskType} {Job : job.JobType} {H : concept.JobTask Job Task}
  {H0 : gel.PriorityPoint Task} {Arrival : job.JobArrival Job} (j j' : Equality.sort Job),
is_true (@concept.same_task Job Task H j j') ->
@definitions.hep_job Job (@gel.GEL Job Task H0 Arrival H) j j' =
(@job.job_arrival Job Arrival j <= @job.job_arrival Job Arrival j')

hep_job_arrival_gel is not universe polymorphic
Arguments hep_job_arrival_gel {Task Job H H0 Arrival} j j' _
hep_job_arrival_gel is opaque
Expands to: Constant prosa.analysis.facts.priority.gel.hep_job_arrival_gel
Declared in library prosa.analysis.facts.priority.gel, line 24, characters 7-26
@hep_job_arrival_gel
     : forall (Task : concept.TaskType) (Job : job.JobType) (H : concept.JobTask Job Task)
         (H0 : gel.PriorityPoint Task) (Arrival : job.JobArrival Job) (j j' : Equality.sort Job),
       is_true (@concept.same_task Job Task H j j') ->
       @definitions.hep_job Job (@gel.GEL Job Task H0 Arrival H) j j' =
       (@job.job_arrival Job Arrival j <= @job.job_arrival Job Arrival j')
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Gel.hep_job_arrival_gel : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  [Arrival : Prosa.Behavior.Job.JobArrival Job] (j j' : Job),
  Prosa.Model.Task.Concept.same_task j j' = true →
    Prosa.Model.Priority.Definitions.hep_job j j' =
      decide (Prosa.Behavior.Job.job_arrival j ≤ Prosa.Behavior.Job.job_arrival j')
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Gel_hep_job_arrival_gel
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Arrival : Prosa_Behavior_Job_JobArrival Job
                      inst_7)
         (j j' : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_same_task Job
            inst_7 Task
            inst_3
            inst_10 j j')
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_14 Arrival
               inst_10)
            j j')
         (Decidable_decide
            (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 Arrival j)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 Arrival j'))
            (Nat_decLe
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 Arrival j)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 Arrival j')))
```
