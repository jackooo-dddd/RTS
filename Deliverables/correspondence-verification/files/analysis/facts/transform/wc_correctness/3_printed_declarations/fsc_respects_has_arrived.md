# `fsc_respects_has_arrived`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.fsc_respects_has_arrived`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.fsc_respects_has_arrived`
- Certificate: `fsc_respects_has_arrived_correspondence`

## Official Rocq

```coq
fsc_respects_has_arrived :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
@jobs_must_be_ready_to_execute Job H (processor_state Job) sched H0
  (@basic.basic_ready_instance Job (processor_state Job) H H0) ->
forall (j : Equality.sort Job) (t : instant),
is_true (sched (@find_swap_candidate Job H H1 arr_seq sched t) == @Some (Equality.sort Job) j) ->
is_true (@has_arrived Job H j t)

fsc_respects_has_arrived is not universe polymorphic
Arguments fsc_respects_has_arrived {Job H H0 H1} arr_seq sched H_jobs_must_be_ready j t _
fsc_respects_has_arrived is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.fsc_respects_has_arrived
Declared in library prosa.analysis.facts.transform.wc_correctness, line 80, characters 10-34
@fsc_respects_has_arrived
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
       @jobs_must_be_ready_to_execute Job H (processor_state Job) sched H0
         (@basic.basic_ready_instance Job (processor_state Job) H H0) ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (sched (@find_swap_candidate Job H H1 arr_seq sched t) == @Some (Equality.sort Job) j) ->
       is_true (@has_arrived Job H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.fsc_respects_has_arrived : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      sched (Prosa.Analysis.Transform.WcTrans.find_swap_candidate arr_seq sched t) = some j →
        Prosa.Behavior.Arrival_sequence.has_arrived j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_fsc_respects_has_arrived
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_6
            inst_9) ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3))
         (sched
            (Prosa_Analysis_Transform_WcTrans_find_swap_candidate Job
               inst_3
               inst_6
               inst_12 arr_seq
               sched t))
         (Option_some Job j) ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_has_arrived Job
            inst_3
            inst_6 j t)
         Bool_true
```
