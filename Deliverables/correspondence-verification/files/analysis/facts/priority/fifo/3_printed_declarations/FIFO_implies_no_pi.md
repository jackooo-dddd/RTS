# `FIFO_implies_no_pi`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.fifo.FIFO_implies_no_pi`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.FIFO_implies_no_pi`
- Certificate: `FIFO_implies_no_pi_correspondence`

## Official Rocq

```coq
FIFO_implies_no_pi :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall sched : @schedule Job PState,
@valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
forall {H : JobPreemptable Job},
@valid_preemption_model Job Cost H PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H
  (@basic_ready_instance Job PState Arrival Cost) arr_seq sched (@FIFO Job Arrival) ->
forall {Task : TaskType} {H0 : JobTask Job Task} (tsk : Equality.sort Task),
@valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
@priority_inversion_is_bounded_by Task Job H0 Arrival Cost PState arr_seq sched (@FIFO Job Arrival) tsk
  (@constant duration nat 0)

FIFO_implies_no_pi is not universe polymorphic
Arguments FIFO_implies_no_pi {Job Arrival Cost} arr_seq H_valid_arrivals {PState} 
  H_uniproc sched H_schedule_is_valid {H} H_valid_preemption_model H_respects_policy 
  {Task H0} tsk H_valid_schedule j _ _ _ t1 t2 _
FIFO_implies_no_pi is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.FIFO_implies_no_pi
Declared in library prosa.analysis.facts.priority.fifo, line 149, characters 10-28
@FIFO_implies_no_pi
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall sched : @schedule Job PState,
       @valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
       forall H : JobPreemptable Job,
       @valid_preemption_model Job Cost H PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H
         (@basic_ready_instance Job PState Arrival Cost) arr_seq sched (@FIFO Job Arrival) ->
       forall (Task : TaskType) (H0 : JobTask Job Task) (tsk : Equality.sort Task),
       @valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
       @priority_inversion_is_bounded_by Task Job H0 Arrival Cost PState arr_seq sched 
         (@FIFO Job Arrival) tsk (@constant duration nat 0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.FIFO_implies_no_pi : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                    (Prosa.Model.Priority.Fifo.FIFO Job) →
                  ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst_4 : DecidableEq Task]
                    [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task] (tsk : Task),
                    Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                      Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq sched tsk
                        (Prosa.Util.Notation.constant 0)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_FIFO_implies_no_pi
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_6
            inst_9)
         arr_seq ->
       forall
         inst_41 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_41 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_41
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_6
            inst_9)
         arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_3
            inst_6) ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_62 : DecidableEq Task)
         (inst_65 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_62)
         (tsk : Task),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_6
            inst_9)
         arr_seq ->
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by Task
         inst_62 Job
         inst_3
         inst_65
         inst_6
         inst_9 PState arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_3
            inst_6)
         tsk
         (Prosa_Util_Notation_constant_inst3 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
```
