# `reflexive_priorities_FP_implies_JLFP`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.coercion.reflexive_priorities_FP_implies_JLFP`
- Lean: `Prosa.Model.Priority.Coercion.reflexive_priorities_FP_implies_JLFP`
- Certificate: `reflexive_priorities_FP_implies_JLFP_correspondence`

## Official Rocq

```coq
reflexive_priorities_FP_implies_JLFP :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} (fp : FP_policy Task),
@reflexive_task_priorities Task fp -> @reflexive_job_priorities Job (@FP_to_JLFP Job Task H fp)

reflexive_priorities_FP_implies_JLFP is not universe polymorphic
Arguments reflexive_priorities_FP_implies_JLFP {Task Job H} fp _ x
reflexive_priorities_FP_implies_JLFP is opaque
Expands to: Constant prosa.model.priority.coercion.reflexive_priorities_FP_implies_JLFP
Declared in library prosa.model.priority.coercion, line 66, characters 8-44
@reflexive_priorities_FP_implies_JLFP
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (fp : FP_policy Task),
       @reflexive_task_priorities Task fp -> @reflexive_job_priorities Job (@FP_to_JLFP Job Task H fp)
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.reflexive_priorities_FP_implies_JLFP : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (fp : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities fp →
    Prosa.Model.Priority.Definitions.reflexive_job_priorities (Prosa.Model.Priority.Coercion.FP_to_JLFP fp)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_reflexive_priorities_FP_implies_JLFP
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
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 fp ->
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_10 fp)
```
