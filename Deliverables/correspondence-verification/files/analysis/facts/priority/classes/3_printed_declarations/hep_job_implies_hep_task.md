# `hep_job_implies_hep_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.hep_job_implies_hep_task`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.hep_job_implies_hep_task`
- Certificate: `hep_job_implies_hep_task_correspondence`

## Official Rocq

```coq
hep_job_implies_hep_task :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} (JLFP : JLFP_policy Job)
  (FP : FP_policy Task),
@JLFP_FP_compatible Task Job H JLFP FP ->
forall j1 j2 : Equality.sort Job,
is_true (@hep_job Job JLFP j1 j2) ->
is_true (@hep_task Task FP (@job_task Job Task H j1) (@job_task Job Task H j2))

hep_job_implies_hep_task is not universe polymorphic
Arguments hep_job_implies_hep_task {Task Job H} JLFP FP H_compatible j1 j2 _
hep_job_implies_hep_task is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.hep_job_implies_hep_task
Declared in library prosa.analysis.facts.priority.classes, line 283, characters 8-32
@hep_job_implies_hep_task
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (JLFP : JLFP_policy Job)
         (FP : FP_policy Task),
       @JLFP_FP_compatible Task Job H JLFP FP ->
       forall j1 j2 : Equality.sort Job,
       is_true (@hep_job Job JLFP j1 j2) ->
       is_true (@hep_task Task FP (@job_task Job Task H j1) (@job_task Job Task H j2))
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.hep_job_implies_hep_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible JLFP FP →
    ∀ (j1 j2 : Job),
      Prosa.Model.Priority.Definitions.hep_job j1 j2 = true →
        Prosa.Model.Priority.Definitions.hep_task (Prosa.Model.Task.Concept.job_task j1)
            (Prosa.Model.Task.Concept.job_task j2) =
          true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_hep_job_implies_hep_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task
         inst_3 Job
         inst_7
         inst_10 JLFP FP ->
       forall j1 j2 : Job,
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7 JLFP j1 j2)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
            inst_3 FP
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_10 j1)
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_10 j2))
         Bool_true
```
