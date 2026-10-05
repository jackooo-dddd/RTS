# `ELF_is_total`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.elf.ELF_is_total`
- Lean: `Prosa.Analysis.Facts.Priority.Elf.ELF_is_total`
- Certificate: `ELF_is_total_correspondence`

## Official Rocq

```coq
ELF_is_total :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {AR : JobArrival Job} (FP : FP_policy Task),
@total_task_priorities Task FP -> @total_job_priorities Job (@ELF Task H Job AR H0 FP)

ELF_is_total is not universe polymorphic
Arguments ELF_is_total {Task H Job H0 AR} FP H_total_priorities x y
ELF_is_total is opaque
Expands to: Constant prosa.analysis.facts.priority.elf.ELF_is_total
Declared in library prosa.analysis.facts.priority.elf, line 74, characters 8-20
@ELF_is_total
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (AR : JobArrival Job) (FP : FP_policy Task),
       @total_task_priorities Task FP -> @total_job_priorities Job (@ELF Task H Job AR H0 FP)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Elf.ELF_is_total : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [AR : Prosa.Behavior.Job.JobArrival Job]
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.total_task_priorities FP →
    Prosa.Model.Priority.Definitions.total_job_priorities (Prosa.Model.Priority.Elf.ELF FP)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Elf_ELF_is_total
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
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_total_job_priorities Job
         inst_7
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_10 Job
            inst_7 AR
            inst_13 FP)
```
