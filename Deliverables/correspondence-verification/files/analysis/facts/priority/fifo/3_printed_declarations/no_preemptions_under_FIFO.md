# `no_preemptions_under_FIFO`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.fifo.no_preemptions_under_FIFO`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.no_preemptions_under_FIFO`
- Certificate: `no_preemptions_under_FIFO_correspondence`

## Official Rocq

```coq
no_preemptions_under_FIFO :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall sched : @schedule Job PState,
@valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
@work_conserving Job Arrival Cost PState (@basic_ready_instance Job PState Arrival Cost) arr_seq sched ->
forall {H : JobPreemptable Job},
@valid_preemption_model Job Cost H PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H
  (@basic_ready_instance Job PState Arrival Cost) arr_seq sched (@FIFO Job Arrival) ->
@no_superfluous_preemptions Job Cost (@JLFP_to_JLDP Job (@FIFO Job Arrival)) PState sched ->
forall (j : Equality.sort Job) (t : instant), is_true (~~ @preempted_at Job Cost PState sched j t)

no_preemptions_under_FIFO is not universe polymorphic
Arguments no_preemptions_under_FIFO {Job Arrival Cost} arr_seq H_valid_arrivals {PState} 
  H_uniproc sched H_schedule_is_valid H_work_conservation {H} H_valid_preemption_model 
  H_respects_policy H_no_superfluous_preemptions j t
no_preemptions_under_FIFO is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.no_preemptions_under_FIFO
Declared in library prosa.analysis.facts.priority.fifo, line 211, characters 8-33
@no_preemptions_under_FIFO
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall sched : @schedule Job PState,
       @valid_schedule Job Arrival PState sched Cost (@basic_ready_instance Job PState Arrival Cost) arr_seq ->
       @work_conserving Job Arrival Cost PState (@basic_ready_instance Job PState Arrival Cost) arr_seq sched ->
       forall H : JobPreemptable Job,
       @valid_preemption_model Job Cost H PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H
         (@basic_ready_instance Job PState Arrival Cost) arr_seq sched (@FIFO Job Arrival) ->
       @no_superfluous_preemptions Job Cost (@JLFP_to_JLDP Job (@FIFO Job Arrival)) PState sched ->
       forall (j : Equality.sort Job) (t : instant), is_true (~~ @preempted_at Job Cost PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.no_preemptions_under_FIFO : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
              ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                  Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                      (Prosa.Model.Priority.Fifo.FIFO Job) →
                    Prosa.Model.Preemption.Parameter.no_superfluous_preemptions sched →
                      ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                        (!Prosa.Model.Preemption.Parameter.preempted_at sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_no_preemptions_under_FIFO
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
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_6
            inst_9)
         arr_seq sched ->
       forall
         inst_48 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_48 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_48
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_6
            inst_9)
         arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_3
            inst_6) ->
       Prosa_Model_Preemption_Parameter_no_superfluous_preemptions Job
         inst_3
         inst_9
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_3
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_3
               inst_6))
         PState sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Model_Preemption_Parameter_preempted_at Job
               inst_3
               inst_9 PState sched j t))
         Bool_true
```
