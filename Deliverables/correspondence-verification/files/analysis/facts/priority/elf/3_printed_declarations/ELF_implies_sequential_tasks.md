# `ELF_implies_sequential_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.elf.ELF_implies_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Elf.ELF_implies_sequential_tasks`
- Certificate: `ELF_implies_sequential_tasks_correspondence`

## Official Rocq

```coq
ELF_implies_sequential_tasks :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobCost Job} {AR : JobArrival Job} (FP : FP_policy Task),
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job AR arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {H2 : @JobReady Job PState H1 AR},
@work_bearing_readiness Job AR H1 PState H2 arr_seq sched (@ELF Task H Job AR H0 FP) ->
@valid_schedule Job AR PState sched H1 H2 arr_seq ->
forall {H3 : JobPreemptable Job},
@valid_preemption_model Job H1 H3 PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job AR H1 PState H3 H2 arr_seq sched (@ELF Task H Job AR H0 FP) ->
@sequential_tasks Job Task H0 AR H1 PState arr_seq sched

ELF_implies_sequential_tasks is not universe polymorphic
Arguments ELF_implies_sequential_tasks {Task H Job H0 H1 AR} FP H_reflexive_priorities
  H_transitive_priorities arr_seq H_valid_arrivals {PState} H_uniproc sched {H2} 
  H_job_ready H_sched_valid {H3} H_valid_preemption_model H_respects_policy j1 j2 
  t _ _ _ _ _
ELF_implies_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.elf.ELF_implies_sequential_tasks
Declared in library prosa.analysis.facts.priority.elf, line 140, characters 10-38
@ELF_implies_sequential_tasks
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobCost Job) (AR : JobArrival Job) (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job AR arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (H2 : @JobReady Job PState H1 AR),
       @work_bearing_readiness Job AR H1 PState H2 arr_seq sched (@ELF Task H Job AR H0 FP) ->
       @valid_schedule Job AR PState sched H1 H2 arr_seq ->
       forall H3 : JobPreemptable Job,
       @valid_preemption_model Job H1 H3 PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job AR H1 PState H3 H2 arr_seq sched
         (@ELF Task H Job AR H0 FP) ->
       @sequential_tasks Job Task H0 AR H1 PState arr_seq sched
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
@Prosa.Analysis.Facts.Priority.Elf.ELF_implies_sequential_tasks : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] [AR : Prosa.Behavior.Job.JobArrival Job]
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
            Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
              ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [H2 : Prosa.Behavior.Ready.JobReady Job PState],
                Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                    ∀ [inst_5 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                      Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                        Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                            (Prosa.Model.Priority.Elf.ELF FP) →
                          Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Elf_ELF_implies_sequential_tasks
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
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (AR : Prosa_Behavior_Job_JobArrival Job
                 inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7 AR arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (H2 : Prosa_Behavior_Ready_JobReady Job
                 inst_7 PState
                 inst_17 AR),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_7 AR
         inst_17 PState H2 arr_seq sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_10 Job
            inst_7 AR
            inst_13 FP) ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7 AR PState sched
         inst_17 H2 arr_seq ->
       forall
         inst_73 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_7
         inst_17
         inst_73 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_7 AR
         inst_17 PState
         inst_73 H2 arr_seq sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_10 Job
            inst_7 AR
            inst_13 FP) ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_13 AR
         inst_17 PState arr_seq sched
```
