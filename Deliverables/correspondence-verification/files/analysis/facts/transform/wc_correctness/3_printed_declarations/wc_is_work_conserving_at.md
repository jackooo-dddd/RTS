# `wc_is_work_conserving_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving_at`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.wc_is_work_conserving_at`
- Certificate: `wc_is_work_conserving_at_correspondence`

## Official Rocq

```coq
wc_is_work_conserving_at :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job (processor_state Job),
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
forall (j : Equality.sort Job) (t : instant),
is_true
  (@job_ready Job (processor_state Job) H0 H (@basic.basic_ready_instance Job (processor_state Job) H H0)
     (@wc_transform Job H H1 arr_seq sched) j t) ->
@arrives_in Job arr_seq j ->
exists j' : Equality.sort Job, @wc_transform Job H H1 arr_seq sched t = @Some (Equality.sort Job) j'

wc_is_work_conserving_at is not universe polymorphic
Arguments wc_is_work_conserving_at {Job H H0 H1} arr_seq H_arr_seq_valid sched
  H_all_deadlines_of_arrivals_met j t _ _
wc_is_work_conserving_at is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving_at
Declared in library prosa.analysis.facts.transform.wc_correctness, line 632, characters 8-32
@wc_is_work_conserving_at
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true
         (@job_ready Job (processor_state Job) H0 H
            (@basic.basic_ready_instance Job (processor_state Job) H H0)
            (@wc_transform Job H H1 arr_seq sched) j t) ->
       @arrives_in Job arr_seq j ->
       exists j' : Equality.sort Job, @wc_transform Job H H1 arr_seq sched t = @Some (Equality.sort Job) j'
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.wc_is_work_conserving_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
        ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Ready.job_ready (Prosa.Analysis.Transform.WcTrans.wc_transform arr_seq sched) j t = true →
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
              ∃ j', Prosa.Analysis.Transform.WcTrans.wc_transform arr_seq sched t = some j'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_wc_is_work_conserving_at
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
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_3
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_3),
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_9
            inst_6
            (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               inst_6
               inst_9)
            (Prosa_Analysis_Transform_WcTrans_wc_transform Job
               inst_3
               inst_6
               inst_12 arr_seq
               sched)
            j t)
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       Exists Job
         (fun j' : Job =>
          Prosa_Analysis_Transform_WcTrans_wc_transform Job
            inst_3
            inst_6
            inst_12 arr_seq sched
            t =
          Option_some Job j')
```
