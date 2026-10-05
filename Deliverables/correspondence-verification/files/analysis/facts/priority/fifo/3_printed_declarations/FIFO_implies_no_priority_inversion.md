# `FIFO_implies_no_priority_inversion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.fifo.FIFO_implies_no_priority_inversion`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.FIFO_implies_no_priority_inversion`
- Certificate: `FIFO_implies_no_priority_inversion_correspondence`

## Official Rocq

```coq
FIFO_implies_no_priority_inversion :
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
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true (@pending Job PState sched Cost Arrival j t) ->
is_true (~~ @priority_inversion Job PState arr_seq sched (@FIFO Job Arrival) j t)

FIFO_implies_no_priority_inversion is not universe polymorphic
Arguments FIFO_implies_no_priority_inversion {Job Arrival Cost} arr_seq H_valid_arrivals 
  {PState} H_uniproc sched H_schedule_is_valid {H} H_valid_preemption_model H_respects_policy 
  j t _ _
FIFO_implies_no_priority_inversion is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.FIFO_implies_no_priority_inversion
Declared in library prosa.analysis.facts.priority.fifo, line 94, characters 8-42
@FIFO_implies_no_priority_inversion
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
       forall (j : Equality.sort Job) (t : instant),
       @arrives_in Job arr_seq j ->
       is_true (@pending Job PState sched Cost Arrival j t) ->
       is_true (~~ @priority_inversion Job PState arr_seq sched (@FIFO Job Arrival) j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.FIFO_implies_no_priority_inversion : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
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
                  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                      Prosa.Behavior.Service.pending sched j t = true →
                        (!Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_FIFO_implies_no_priority_inversion
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
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_9
            inst_6 j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion Job
               inst_3 PState arr_seq sched
               (Prosa_Model_Priority_Fifo_FIFO Job
                  inst_3
                  inst_6)
               j t))
         Bool_true
```
