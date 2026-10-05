# `elf_generalizes_fixed_priority`

- Kind (Rocq): Remark
- Rocq: `prosa.results.generality.elf.elf_generalizes_fixed_priority`
- Lean: `Prosa.Results.Generality.Elf.elf_generalizes_fixed_priority`
- Certificate: `elf_generalizes_fixed_priority_correspondence`

## Official Rocq

```coq
elf_generalizes_fixed_priority :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H1 : JobTask Job Task}
  {PState : ProcessorState Job} {Arrival : JobArrival Job} {Cost : JobCost Job} {H2 : JobPreemptable Job}
  {JR : @JobReady Job PState Cost Arrival} (fp : FP_policy Task),
(forall tsk1 tsk2 : Equality.sort Task, is_true (tsk1 != tsk2) -> is_true (~~ @ep_task Task fp tsk1 tsk2)) ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@valid_schedule Job Arrival PState sched Cost JR arr_seq ->
@sequential_tasks Job Task H1 Arrival Cost PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H2 JR arr_seq sched
  (@ELF Task H Job Arrival H1 fp) <->
@respects_FP_policy_at_preemption_point Task Job H1 Arrival Cost PState H2 JR arr_seq sched fp

elf_generalizes_fixed_priority is not universe polymorphic
Arguments elf_generalizes_fixed_priority {Task H Job H1 PState Arrival Cost H2 JR} 
  fp H_distinct_fixed_priorities%function_scope arr_seq sched H_sched_valid H_sequential
elf_generalizes_fixed_priority is opaque
Expands to: Constant prosa.results.generality.elf.elf_generalizes_fixed_priority
Declared in library prosa.results.generality.elf, line 104, characters 11-41
@elf_generalizes_fixed_priority
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H1 : JobTask Job Task)
         (PState : ProcessorState Job) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H2 : JobPreemptable Job) (JR : @JobReady Job PState Cost Arrival) (fp : FP_policy Task),
       (forall tsk1 tsk2 : Equality.sort Task,
        is_true (tsk1 != tsk2) -> is_true (~~ @ep_task Task fp tsk1 tsk2)) ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @valid_schedule Job Arrival PState sched Cost JR arr_seq ->
       @sequential_tasks Job Task H1 Arrival Cost PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H2 JR arr_seq sched
         (@ELF Task H Job Arrival H1 fp) <->
       @respects_FP_policy_at_preemption_point Task Job H1 Arrival Cost PState H2 JR arr_seq sched fp
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
@Prosa.Results.Generality.Elf.elf_generalizes_fixed_priority : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [Arrival : Prosa.Behavior.Job.JobArrival Job]
  [Cost : Prosa.Behavior.Job.JobCost Job] [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  [JR : Prosa.Behavior.Ready.JobReady Job PState] (fp : Prosa.Model.Priority.Definitions.FP_policy Task),
  (∀ (tsk1 tsk2 : Task), decide (tsk1 ≠ tsk2) = true → (!Prosa.Model.Priority.Definitions.ep_task tsk1 tsk2) = true) →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
      (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
          (Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
              (Prosa.Model.Priority.Elf.ELF fp) ↔
            Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched fp)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Generality_Elf_elf_generalizes_fixed_priority
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
                 inst_3),
       (forall tsk1 tsk2 : Task,
        @eq Bool
          (Decidable_decide (Ne Task tsk1 tsk2)
             (instDecidableNot (@eq Task tsk1 tsk2)
                (inst_3 tsk1 tsk2)))
          Bool_true ->
        @eq Bool
          (Bool_not
             (Prosa_Model_Priority_Definitions_ep_task Task
                inst_3 fp tsk1 tsk2))
          Bool_true) ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7 Arrival PState sched Cost JR
         arr_seq ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_13 Arrival Cost PState arr_seq sched ->
       Iff
         (Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
            inst_7 Arrival Cost PState
            inst_23 JR arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_10 Job
               inst_7 Arrival
               inst_13 fp))
         (Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point Task
            inst_3 Job
            inst_7
            inst_13 Arrival Cost PState
            inst_23 JR arr_seq sched fp)
```
