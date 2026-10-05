# `hep_job_elf_gel`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.priority.elf.hep_job_elf_gel`
- Lean: `Prosa.Analysis.Facts.Priority.Elf.hep_job_elf_gel`
- Certificate: `hep_job_elf_gel_correspondence`

## Official Rocq

```coq
hep_job_elf_gel :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {AR : JobArrival Job} (FP : FP_policy Task) (j j' : Equality.sort Job),
is_true (@ep_task Task FP (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
@hep_job Job (@ELF Task H Job AR H0 FP) j j' = @hep_job Job (@GEL Job Task H AR H0) j j'

hep_job_elf_gel is not universe polymorphic
Arguments hep_job_elf_gel {Task H Job H0 AR} FP j j' _
hep_job_elf_gel is opaque
Expands to: Constant prosa.analysis.facts.priority.elf.hep_job_elf_gel
Declared in library prosa.analysis.facts.priority.elf, line 31, characters 9-24
@hep_job_elf_gel
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (AR : JobArrival Job) (FP : FP_policy Task) (j j' : Equality.sort Job),
       is_true (@ep_task Task FP (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
       @hep_job Job (@ELF Task H Job AR H0 FP) j j' = @hep_job Job (@GEL Job Task H AR H0) j j'
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Elf.hep_job_elf_gel : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [AR : Prosa.Behavior.Job.JobArrival Job] (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (j j' : Job),
  Prosa.Model.Priority.Definitions.ep_task (Prosa.Model.Task.Concept.job_task j)
        (Prosa.Model.Task.Concept.job_task j') =
      true →
    Prosa.Model.Priority.Definitions.hep_job j j' = Prosa.Model.Priority.Definitions.hep_job j j'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Elf_hep_job_elf_gel
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
                 inst_3)
         (j j' : Job),
       @eq Bool
         (Prosa_Model_Priority_Definitions_ep_task Task
            inst_3 FP
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_13 j)
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_13 j'))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_10 Job
               inst_7 AR
               inst_13 FP)
            j j')
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_10 AR
               inst_13)
            j j')
```
