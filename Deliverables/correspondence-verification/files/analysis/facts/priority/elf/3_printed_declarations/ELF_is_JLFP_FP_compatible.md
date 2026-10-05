# `ELF_is_JLFP_FP_compatible`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.elf.ELF_is_JLFP_FP_compatible`
- Lean: `Prosa.Analysis.Facts.Priority.Elf.ELF_is_JLFP_FP_compatible`
- Certificate: `ELF_is_JLFP_FP_compatible_correspondence`

## Official Rocq

```coq
ELF_is_JLFP_FP_compatible :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {AR : JobArrival Job} (FP : FP_policy Task),
@JLFP_FP_compatible Task Job H0 (@ELF Task H Job AR H0 FP) FP

ELF_is_JLFP_FP_compatible is not universe polymorphic
Arguments ELF_is_JLFP_FP_compatible {Task H Job H0 AR} FP
ELF_is_JLFP_FP_compatible is opaque
Expands to: Constant prosa.analysis.facts.priority.elf.ELF_is_JLFP_FP_compatible
Declared in library prosa.analysis.facts.priority.elf, line 86, characters 8-33
@ELF_is_JLFP_FP_compatible
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (AR : JobArrival Job) (FP : FP_policy Task),
       @JLFP_FP_compatible Task Job H0 (@ELF Task H Job AR H0 FP) FP
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Elf.ELF_is_JLFP_FP_compatible : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [AR : Prosa.Behavior.Job.JobArrival Job] (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible (Prosa.Model.Priority.Elf.ELF FP) FP
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Elf_ELF_is_JLFP_FP_compatible
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
       Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task
         inst_3 Job
         inst_7
         inst_13
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_10 Job
            inst_7 AR
            inst_13 FP)
         FP
```
