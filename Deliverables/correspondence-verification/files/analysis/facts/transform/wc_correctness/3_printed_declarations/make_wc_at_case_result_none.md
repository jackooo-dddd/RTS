# `make_wc_at_case_result_none`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_none`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_none`
- Certificate: `make_wc_at_case_result_none_correspondence`

## Official Rocq

```coq
make_wc_at_case_result_none :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall (sched : @schedule Job (processor_state Job)) (t : instant),
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true
  (@job_ready Job (processor_state Job) H0 H (@basic.basic_ready_instance Job (processor_state Job) H H0)
     (@make_wc_at Job H H1 arr_seq sched t) j t) ->
@search_result Job H H1 arr_seq sched t = @None nat -> False

make_wc_at_case_result_none is not universe polymorphic
Arguments make_wc_at_case_result_none {Job H H0 H1} arr_seq H_arr_seq_valid sched 
  t H_all_deadlines_of_arrivals_met j H_arrives_in H_job_ready_sched' H_search_result_none
make_wc_at_case_result_none is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_none
Declared in library prosa.analysis.facts.transform.wc_correctness, line 341, characters 14-41
@make_wc_at_case_result_none
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall (sched : @schedule Job (processor_state Job)) (t : instant),
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true
         (@job_ready Job (processor_state Job) H0 H
            (@basic.basic_ready_instance Job (processor_state Job) H H0)
            (@make_wc_at Job H H1 arr_seq sched t) j t) ->
       @search_result Job H H1 arr_seq sched t = @None nat -> False
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_none : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
      (t : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
        ∀ (j : Job),
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            Prosa.Behavior.Ready.job_ready (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq sched t) j t = true →
              Prosa.Analysis.Facts.Transform.WcCorrectness.search_result arr_seq sched t = none → False
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_make_wc_at_case_result_none
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
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
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
            (Prosa_Analysis_Transform_WcTrans_make_wc_at Job
               inst_3
               inst_6
               inst_12 arr_seq
               sched t)
            j t)
         Bool_true ->
       @eq (Option_inst1 Nat)
         (Prosa_Analysis_Facts_Transform_WcCorrectness_search_result Job
            inst_3
            inst_6
            inst_12 arr_seq sched
            t)
         (Option_none_inst1 Nat) ->
       False
```
