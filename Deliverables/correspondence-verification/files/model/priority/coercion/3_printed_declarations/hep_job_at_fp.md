# `hep_job_at_fp`

- Kind (Rocq): Remark
- Rocq: `prosa.model.priority.coercion.hep_job_at_fp`
- Lean: `Prosa.Model.Priority.Coercion.hep_job_at_fp`
- Certificate: `hep_job_at_fp_correspondence`

## Official Rocq

```coq
hep_job_at_fp :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : FP_policy Task}
  (j j' : Equality.sort Job) (t : instant),
@hep_job_at Job (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H H0)) t j j' =
@hep_task Task H0 (@job_task Job Task H j) (@job_task Job Task H j')

hep_job_at_fp is not universe polymorphic
Arguments hep_job_at_fp {Task Job H H0} j j' t
hep_job_at_fp is opaque
Expands to: Constant prosa.model.priority.coercion.hep_job_at_fp
Declared in library prosa.model.priority.coercion, line 57, characters 9-22
@hep_job_at_fp
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : FP_policy Task)
         (j j' : Equality.sort Job) (t : instant),
       @hep_job_at Job (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H H0)) t j j' =
       @hep_task Task H0 (@job_task Job Task H j) (@job_task Job Task H j')
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.hep_job_at_fp : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [fp : Prosa.Model.Priority.Definitions.FP_policy Task] (j j' : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Priority.Definitions.hep_job_at t j j' =
    Prosa.Model.Priority.Definitions.hep_task (Prosa.Model.Task.Concept.job_task j)
      (Prosa.Model.Task.Concept.job_task j')
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_hep_job_at_fp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (fp : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (j j' : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
            inst_7
            (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
               inst_7
               (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
                  inst_7 Task
                  inst_3
                  inst_10 fp))
            t j j')
         (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
            inst_3 fp
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_10 j)
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_10 j'))
```
