# `ELF_respects_sequential_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.elf.ELF_respects_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Elf.ELF_respects_sequential_tasks`
- Certificate: `ELF_respects_sequential_tasks_correspondence`

## Official Rocq

```coq
ELF_respects_sequential_tasks :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {AR : JobArrival Job} (FP : FP_policy Task),
@reflexive_task_priorities Task FP ->
@policy_respects_sequential_tasks Task Job H0 AR (@ELF Task H Job AR H0 FP)

ELF_respects_sequential_tasks is not universe polymorphic
Arguments ELF_respects_sequential_tasks {Task H Job H0 AR} FP H_reflexive_priorities j1 j2 _ _
ELF_respects_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.elf.ELF_respects_sequential_tasks
Declared in library prosa.analysis.facts.priority.elf, line 99, characters 8-37
@ELF_respects_sequential_tasks
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (AR : JobArrival Job) (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       @policy_respects_sequential_tasks Task Job H0 AR (@ELF Task H Job AR H0 FP)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Elf.ELF_respects_sequential_tasks : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [AR : Prosa.Behavior.Job.JobArrival Job] (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks (Prosa.Model.Priority.Elf.ELF FP)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Elf_ELF_respects_sequential_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (AR : Prosa_Behavior_Job_JobArrival Job
                 inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task
         inst_3 Job
         inst_7
         inst_13 AR
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_10 Job
            inst_7 AR
            inst_13 FP)
```
