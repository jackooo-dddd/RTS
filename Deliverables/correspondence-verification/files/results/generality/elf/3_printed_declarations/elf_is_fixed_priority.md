# `elf_is_fixed_priority`

- Kind (Rocq): Remark
- Rocq: `prosa.results.generality.elf.elf_is_fixed_priority`
- Lean: `Prosa.Results.Generality.Elf.elf_is_fixed_priority`
- Certificate: `elf_is_fixed_priority_correspondence`

## Official Rocq

```coq
elf_is_fixed_priority :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H1 : JobTask Job Task}
  {PState : ProcessorState Job} {Arrival : JobArrival Job} {Cost : JobCost Job} {H2 : JobPreemptable Job}
  {JR : @JobReady Job PState Cost Arrival} (fp : FP_policy Task) (sched : @schedule Job PState)
  (arr_seq : arrival_sequence Job),
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H2 JR arr_seq sched
  (@ELF Task H Job Arrival H1 fp) ->
@respects_FP_policy_at_preemption_point Task Job H1 Arrival Cost PState H2 JR arr_seq sched fp

elf_is_fixed_priority is not universe polymorphic
Arguments elf_is_fixed_priority {Task H Job H1 PState Arrival Cost H2 JR} fp sched arr_seq _ j j_hp t _ _ _ _
elf_is_fixed_priority is opaque
Expands to: Constant prosa.results.generality.elf.elf_is_fixed_priority
Declared in library prosa.results.generality.elf, line 70, characters 11-32
@elf_is_fixed_priority
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H1 : JobTask Job Task)
         (PState : ProcessorState Job) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H2 : JobPreemptable Job) (JR : @JobReady Job PState Cost Arrival) (fp : FP_policy Task)
         (sched : @schedule Job PState) (arr_seq : arrival_sequence Job),
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H2 JR arr_seq sched
         (@ELF Task H Job Arrival H1 fp) ->
       @respects_FP_policy_at_preemption_point Task Job H1 Arrival Cost PState H2 JR arr_seq sched fp
```

## Lean

```lean
@Prosa.Results.Generality.Elf.elf_is_fixed_priority : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [Arrival : Prosa.Behavior.Job.JobArrival Job]
  [Cost : Prosa.Behavior.Job.JobCost Job] [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  [JR : Prosa.Behavior.Ready.JobReady Job PState] (fp : Prosa.Model.Priority.Definitions.FP_policy Task)
  (sched : Prosa.Behavior.Schedule.schedule PState) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
      (Prosa.Model.Priority.Elf.ELF fp) →
    Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched fp
```

## Lean, imported into Rocq

```coq
Prosa_Results_Generality_Elf_elf_is_fixed_priority
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Priority_Gel_PriorityPoint
                                                                                Task
                                                                                inst_3)
         (inst_13 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (Arrival : Prosa_Behavior_Job_JobArrival Job
                      inst_7)
         (Cost : Prosa_Behavior_Job_JobCost Job
                   inst_7)
         (inst_23 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                                Job
                                                                                inst_7)
         (JR : Prosa_Behavior_Ready_JobReady Job
                 inst_7 PState Cost Arrival)
         (fp : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_7 Arrival Cost PState
         inst_23 JR arr_seq sched
         (Prosa_Model_Priority_Elf_ELF Task inst_3
            inst_10 Job
            inst_7 Arrival
            inst_13 fp) ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point Task
         inst_3 Job
         inst_7
         inst_13 Arrival Cost PState
         inst_23 JR arr_seq sched fp
```
