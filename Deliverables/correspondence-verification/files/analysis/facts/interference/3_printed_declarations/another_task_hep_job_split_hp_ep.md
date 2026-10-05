# `another_task_hep_job_split_hp_ep`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.another_task_hep_job_split_hp_ep`
- Lean: `Prosa.Analysis.Facts.Interference.another_task_hep_job_split_hp_ep`
- Certificate: `another_task_hep_job_split_hp_ep_correspondence`

## Official Rocq

```coq
another_task_hep_job_split_hp_ep :
forall {Task : TaskType} {Job : JobType} {jt : JobTask Job Task} {FP : FP_policy Task}
  {JLFP : JLFP_policy Job},
@JLFP_FP_compatible Task Job jt JLFP FP ->
forall j1 j2 : Equality.sort Job,
@another_task_hep_job Task Job jt JLFP j1 j2 =
@hp_task_hep_job Task Job jt FP JLFP j1 j2 || @other_ep_task_hep_job Task Job jt FP JLFP j1 j2

another_task_hep_job_split_hp_ep is not universe polymorphic
Arguments another_task_hep_job_split_hp_ep {Task Job jt FP JLFP} H_compatible j1 j2
another_task_hep_job_split_hp_ep is opaque
Expands to: Constant prosa.analysis.facts.interference.another_task_hep_job_split_hp_ep
Declared in library prosa.analysis.facts.interference, line 44, characters 8-40
@another_task_hep_job_split_hp_ep
     : forall (Task : TaskType) (Job : JobType) (jt : JobTask Job Task) (FP : FP_policy Task)
         (JLFP : JLFP_policy Job),
       @JLFP_FP_compatible Task Job jt JLFP FP ->
       forall j1 j2 : Equality.sort Job,
       @another_task_hep_job Task Job jt JLFP j1 j2 =
       @hp_task_hep_job Task Job jt FP JLFP j1 j2 || @other_ep_task_hep_job Task Job jt FP JLFP j1 j2
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.another_task_hep_job_split_hp_ep : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (FP : Prosa.Model.Priority.Definitions.FP_policy Task)
  (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible JLFP FP →
    ∀ (j1 j2 : Job),
      Prosa.Model.Priority.Definitions.another_task_hep_job j1 j2 =
        (Prosa.Analysis.Definitions.Interference.hp_task_hep_job j1 j2 ||
          Prosa.Analysis.Definitions.Interference.other_ep_task_hep_job j1 j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_another_task_hep_job_split_hp_ep
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7),
       Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task
         inst_3 Job
         inst_7
         inst_10 JLFP FP ->
       forall j1 j2 : Job,
       @eq Bool
         (Prosa_Model_Priority_Definitions_another_task_hep_job Task
            inst_3 Job
            inst_7
            inst_10 JLFP j1 j2)
         (Bool_or
            (Prosa_Analysis_Definitions_Interference_hp_task_hep_job Task
               inst_3 Job
               inst_7
               inst_10 FP JLFP j1 j2)
            (Prosa_Analysis_Definitions_Interference_other_ep_task_hep_job Task
               inst_3 Job
               inst_7
               inst_10 FP JLFP j1 j2))
```
