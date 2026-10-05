# `ELF_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.elf.ELF_is_transitive`
- Lean: `Prosa.Analysis.Facts.Priority.Elf.ELF_is_transitive`
- Certificate: `ELF_is_transitive_correspondence`

## Official Rocq

```coq
ELF_is_transitive :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {AR : JobArrival Job} (FP : FP_policy Task),
@transitive_task_priorities Task FP -> @transitive_job_priorities Job (@ELF Task H Job AR H0 FP)

ELF_is_transitive is not universe polymorphic
Arguments ELF_is_transitive {Task H Job H0 AR} FP H_transitive_priorities y x z _ _
ELF_is_transitive is opaque
Expands to: Constant prosa.analysis.facts.priority.elf.ELF_is_transitive
Declared in library prosa.analysis.facts.priority.elf, line 61, characters 8-25
@ELF_is_transitive
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (AR : JobArrival Job) (FP : FP_policy Task),
       @transitive_task_priorities Task FP -> @transitive_job_priorities Job (@ELF Task H Job AR H0 FP)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Elf.ELF_is_transitive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [AR : Prosa.Behavior.Job.JobArrival Job] (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
    Prosa.Model.Priority.Definitions.transitive_job_priorities (Prosa.Model.Priority.Elf.ELF FP)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Elf_ELF_is_transitive
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
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_7
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_10 Job
            inst_7 AR
            inst_13 FP)
```
