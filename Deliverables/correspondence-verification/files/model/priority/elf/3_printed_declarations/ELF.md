# `ELF`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.elf.ELF`
- Lean: `Prosa.Model.Priority.Elf.ELF`
- Certificate: `ELF_correspondence`

## Official Rocq

```coq
ELF :
forall {Task : TaskType},
PriorityPoint Task ->
forall {Job : JobType}, JobArrival Job -> JobTask Job Task -> FP_policy Task -> JLFP_policy Job

ELF is not universe polymorphic
Arguments ELF {Task H Job H0 H1} fp _ _
ELF is transparent
Expands to: Constant prosa.model.priority.elf.ELF
Declared in library prosa.model.priority.elf, line 44, characters 2-728
@ELF
     : forall Task : TaskType,
       PriorityPoint Task ->
       forall Job : JobType, JobArrival Job -> JobTask Job Task -> FP_policy Task -> JLFP_policy Job
```

Body:

```coq
ELF =
fun (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobArrival Job) 
  (H1 : JobTask Job Task) (fp : FP_policy Task) (j1 j2 : Equality.sort Job) =>
let gel_hep_job := @hep_job Job (@GEL Job Task H H0 H1) in
@hp_task Task fp (@job_task Job Task H1 j1) (@job_task Job Task H1 j2)
|| @hep_task Task fp (@job_task Job Task H1 j1) (@job_task Job Task H1 j2) && gel_hep_job j1 j2
     : forall {Task : TaskType},
       PriorityPoint Task ->
       forall {Job : JobType}, JobArrival Job -> JobTask Job Task -> FP_policy Task -> JLFP_policy Job

Arguments ELF {Task H Job H0 H1} fp _ _
New coercion path [GRing.subring_closedM; GRing.smulr_closedN] : GRing.subring_closed >-> GRing.oppr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedM] : GRing.subring_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedD] : GRing.subring_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.submod_closed_semi; GRing.subsemimod_closedD] : GRing.submod_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.subalg_closedBM; GRing.subring_closedB] : GRing.subalg_closed >-> GRing.zmod_closed is ambiguous with existing 
New coercion path [GRing.sdivr_closedM; GRing.smulr_closedM] : GRing.sdivr_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.divring_closed_div; GRing.sdivr_closedM] : GRing.divring_closed >-> GRing.smulr_closed is ambiguous with existing 
New coercion path [GRing.divalg_closedZ; GRing.subalg_closedBM] : GRing.divalg_closed >-> GRing.subring_closed is ambiguous with existing
```

## Lean

```lean
@Prosa.Model.Priority.Elf.ELF : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              Prosa.Model.Priority.Definitions.FP_policy Task → Prosa.Model.Priority.Definitions.JLFP_policy Job
```

Body:

```lean
@[reducible] def Prosa.Model.Priority.Elf.ELF.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              Prosa.Model.Priority.Definitions.FP_policy Task → Prosa.Model.Priority.Definitions.JLFP_policy Job :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] {Job} [DecidableEq Job]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Model.Task.Concept.JobTask Job Task] fp =>
  {
    hep_job := fun j1 j2 =>
      Prosa.Model.Priority.Definitions.hp_task (Prosa.Model.Task.Concept.job_task j1)
          (Prosa.Model.Task.Concept.job_task j2) ||
        Prosa.Model.Priority.Definitions.hep_task (Prosa.Model.Task.Concept.job_task j1)
            (Prosa.Model.Task.Concept.job_task j2) &&
          Prosa.Model.Priority.Definitions.hep_job j1 j2 }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Elf_ELF
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_10
```

Body:

```coq
Prosa_Model_Priority_Elf_ELF@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Priority_Gel_PriorityPoint Task
                                                                    inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Behavior_Job_JobArrival Job
                                                                     inst_10)
  (inst_16 : Prosa_Model_Task_Concept_JobTask Job
                                                                     inst_10
                                                                     Task
                                                                     inst_3)
  (fp : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3) =>
Prosa_Model_Priority_Definitions_JLFP_policy_mk Job
  inst_10
  (fun j1 j2 : Job =>
   Bool_or
     (Prosa_Model_Priority_Definitions_hp_task Task
        inst_3 fp
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_10 Task
           inst_3
           inst_16 j1)
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_10 Task
           inst_3
           inst_16 j2))
     (Bool_and
        (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
           inst_3 fp
           (Prosa_Model_Task_Concept_JobTask_job_task Job
              inst_10 Task
              inst_3
              inst_16 j1)
           (Prosa_Model_Task_Concept_JobTask_job_task Job
              inst_10 Task
              inst_3
              inst_16 j2))
        (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
           inst_10
           (Prosa_Model_Priority_Gel_GEL Job inst_10
              Task inst_3
              inst_6
              inst_13
              inst_16)
           j1 j2)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_10

Arguments Prosa_Model_Priority_Elf_ELF Task inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_16 fp
```
