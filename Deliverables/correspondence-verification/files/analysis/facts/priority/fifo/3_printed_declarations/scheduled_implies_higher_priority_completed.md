# `scheduled_implies_higher_priority_completed`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.fifo.scheduled_implies_higher_priority_completed`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.scheduled_implies_higher_priority_completed`
- Certificate: `scheduled_implies_higher_priority_completed_correspondence`

## Official Rocq

```coq
scheduled_implies_higher_priority_completed :
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
is_true (@scheduled_at Job PState sched j t) ->
forall j_hp : Equality.sort Job,
@arrives_in Job arr_seq j_hp ->
is_true (~~ @hep_job Job (@FIFO Job Arrival) j j_hp) -> is_true (@completed_by Job PState sched Cost j_hp t)

scheduled_implies_higher_priority_completed is not universe polymorphic
Arguments scheduled_implies_higher_priority_completed {Job Arrival Cost} arr_seq 
  H_valid_arrivals {PState} H_uniproc sched H_schedule_is_valid {H} H_valid_preemption_model
  H_respects_policy j t _ j_hp _ _
scheduled_implies_higher_priority_completed is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.scheduled_implies_higher_priority_completed
Declared in library prosa.analysis.facts.priority.fifo, line 111, characters 8-51
@scheduled_implies_higher_priority_completed
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
       is_true (@scheduled_at Job PState sched j t) ->
       forall j_hp : Equality.sort Job,
       @arrives_in Job arr_seq j_hp ->
       is_true (~~ @hep_job Job (@FIFO Job Arrival) j j_hp) ->
       is_true (@completed_by Job PState sched Cost j_hp t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.scheduled_implies_higher_priority_completed : ∀ {Job : Prosa.Behavior.Job.JobType}
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
                    Prosa.Behavior.Service.scheduled_at sched j t = true →
                      ∀ (j_hp : Job),
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j_hp →
                          (!Prosa.Model.Priority.Definitions.hep_job j j_hp) = true →
                            Prosa.Behavior.Service.completed_by sched j_hp t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_scheduled_implies_higher_priority_completed
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
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       forall j_hp : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j_hp ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3
               (Prosa_Model_Priority_Fifo_FIFO Job
                  inst_3
                  inst_6)
               j j_hp))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_9 j_hp t)
         Bool_true
```
