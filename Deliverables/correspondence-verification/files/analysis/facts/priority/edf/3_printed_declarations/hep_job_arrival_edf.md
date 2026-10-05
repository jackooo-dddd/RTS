# `hep_job_arrival_edf`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.edf.hep_job_arrival_edf`
- Lean: `Prosa.Analysis.Facts.Priority.Edf.hep_job_arrival_edf`
- Certificate: `hep_job_arrival_edf_correspondence`

## Official Rocq

```coq
hep_job_arrival_edf :
forall {Job : JobType} {H : JobArrival Job} {Task : TaskType} {H0 : TaskDeadline Task}
  {H1 : JobTask Job Task} (j j' : Equality.sort Job),
is_true (@same_task Job Task H1 j j') ->
@hep_job Job (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H H1)) j j' =
(@job_arrival Job H j <= @job_arrival Job H j')

hep_job_arrival_edf is not universe polymorphic
Arguments hep_job_arrival_edf {Job H Task H0 H1} j j' _
hep_job_arrival_edf is opaque
Expands to: Constant prosa.analysis.facts.priority.edf.hep_job_arrival_edf
Declared in library prosa.analysis.facts.priority.edf, line 47, characters 9-28
@hep_job_arrival_edf
     : forall (Job : JobType) (H : JobArrival Job) (Task : TaskType) (H0 : TaskDeadline Task)
         (H1 : JobTask Job Task) (j j' : Equality.sort Job),
       is_true (@same_task Job Task H1 j j') ->
       @hep_job Job (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H H1)) j j' =
       (@job_arrival Job H j <= @job_arrival Job H j')
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Edf.hep_job_arrival_edf : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_2 : DecidableEq Task]
  [inst_3 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  (j j' : Job),
  Prosa.Model.Task.Concept.same_task j j' = true →
    Prosa.Model.Priority.Definitions.hep_job j j' =
      decide (Prosa.Behavior.Job.job_arrival j ≤ Prosa.Behavior.Job.job_arrival j')
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Edf_hep_job_arrival_edf
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_10 : DecidableEq Task)
         (inst_13 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_10)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_10)
         (j j' : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_same_task Job
            inst_3 Task
            inst_10
            inst_16 j j')
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3
            (Prosa_Model_Priority_Edf_EDF Job
               inst_3
               (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                  inst_3
                  inst_10
                  inst_13
                  inst_6
                  inst_16))
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
