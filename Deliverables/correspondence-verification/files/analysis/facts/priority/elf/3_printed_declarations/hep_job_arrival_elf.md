# `hep_job_arrival_elf`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.elf.hep_job_arrival_elf`
- Lean: `Prosa.Analysis.Facts.Priority.Elf.hep_job_arrival_elf`
- Certificate: `hep_job_arrival_elf_correspondence`

## Official Rocq

```coq
hep_job_arrival_elf :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {AR : JobArrival Job} (FP : FP_policy Task),
@reflexive_task_priorities Task FP ->
forall j j' : Equality.sort Job,
is_true (@same_task Job Task H0 j j') ->
@hep_job Job (@ELF Task H Job AR H0 FP) j j' = (@job_arrival Job AR j <= @job_arrival Job AR j')

hep_job_arrival_elf is not universe polymorphic
Arguments hep_job_arrival_elf {Task H Job H0 AR} FP H_reflexive_priorities j j' _
hep_job_arrival_elf is opaque
Expands to: Constant prosa.analysis.facts.priority.elf.hep_job_arrival_elf
Declared in library prosa.analysis.facts.priority.elf, line 45, characters 7-26
@hep_job_arrival_elf
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (AR : JobArrival Job) (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       forall j j' : Equality.sort Job,
       is_true (@same_task Job Task H0 j j') ->
       @hep_job Job (@ELF Task H Job AR H0 FP) j j' = (@job_arrival Job AR j <= @job_arrival Job AR j')
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Elf.hep_job_arrival_elf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [AR : Prosa.Behavior.Job.JobArrival Job] (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    ∀ (j j' : Job),
      Prosa.Model.Task.Concept.same_task j j' = true →
        Prosa.Model.Priority.Definitions.hep_job j j' =
          decide (Prosa.Behavior.Job.job_arrival j ≤ Prosa.Behavior.Job.job_arrival j')
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Elf_hep_job_arrival_elf
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
       forall j j' : Job,
       @eq Bool
         (Prosa_Model_Task_Concept_same_task Job
            inst_7 Task
            inst_3
            inst_13 j j')
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
         (Decidable_decide
            (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 AR j)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 AR j'))
            (Nat_decLe
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 AR j)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7 AR j')))
```
