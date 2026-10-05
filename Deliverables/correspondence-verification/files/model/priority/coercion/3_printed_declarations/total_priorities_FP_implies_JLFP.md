# `total_priorities_FP_implies_JLFP`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.coercion.total_priorities_FP_implies_JLFP`
- Lean: `Prosa.Model.Priority.Coercion.total_priorities_FP_implies_JLFP`
- Certificate: `total_priorities_FP_implies_JLFP_correspondence`

## Official Rocq

```coq
total_priorities_FP_implies_JLFP :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} (fp : FP_policy Task),
@total_task_priorities Task fp -> @total_job_priorities Job (@FP_to_JLFP Job Task H fp)

total_priorities_FP_implies_JLFP is not universe polymorphic
Arguments total_priorities_FP_implies_JLFP {Task Job H} fp _ x y
total_priorities_FP_implies_JLFP is opaque
Expands to: Constant prosa.model.priority.coercion.total_priorities_FP_implies_JLFP
Declared in library prosa.model.priority.coercion, line 80, characters 8-40
@total_priorities_FP_implies_JLFP
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (fp : FP_policy Task),
       @total_task_priorities Task fp -> @total_job_priorities Job (@FP_to_JLFP Job Task H fp)
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.total_priorities_FP_implies_JLFP : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (fp : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.total_task_priorities fp →
    Prosa.Model.Priority.Definitions.total_job_priorities (Prosa.Model.Priority.Coercion.FP_to_JLFP fp)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_total_priorities_FP_implies_JLFP
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
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3 fp ->
       Prosa_Model_Priority_Definitions_total_job_priorities Job
         inst_7
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_10 fp)
```
