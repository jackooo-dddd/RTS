# `make_wc_at_case_result_found`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_found`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_found`
- Certificate: `make_wc_at_case_result_found_correspondence`

## Official Rocq

```coq
make_wc_at_case_result_found :
forall {Job : JobType} {H : JobArrival Job} {H1 : JobDeadline Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t : instant),
is_true (@ideal_is_idle Job sched t) ->
forall t_swap : instant,
@search_result Job H H1 arr_seq sched t = @Some instant t_swap ->
exists j : Equality.sort Job,
  @swapped Job (processor_state Job) sched t t_swap t = @Some (Equality.sort Job) j

make_wc_at_case_result_found is not universe polymorphic
Arguments make_wc_at_case_result_found {Job H H1} arr_seq sched t H_sched_t_idle t_swap search_result_found
make_wc_at_case_result_found is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_found
Declared in library prosa.analysis.facts.transform.wc_correctness, line 245, characters 14-42
@make_wc_at_case_result_found
     : forall (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (t : instant),
       is_true (@ideal_is_idle Job sched t) ->
       forall t_swap : instant,
       @search_result Job H H1 arr_seq sched t = @Some instant t_swap ->
       exists j : Equality.sort Job,
         @swapped Job (processor_state Job) sched t t_swap t = @Some (Equality.sort Job) j
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.make_wc_at_case_result_found : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Ideal.ideal_is_idle sched t = true →
    ∀ (t_swap : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Facts.Transform.WcCorrectness.search_result arr_seq sched t = some t_swap →
        ∃ j, Prosa.Analysis.Transform.Swap.swapped sched t t_swap t = some j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_make_wc_at_case_result_found
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Ideal_ideal_is_idle Job
            inst_3 sched t)
         Bool_true ->
       forall t_swap : Prosa_Behavior_Time_instant,
       @eq (Option_inst1 Nat)
         (Prosa_Analysis_Facts_Transform_WcCorrectness_search_result Job
            inst_3
            inst_6
            inst_9 arr_seq sched t)
         (Option_some_inst1 Prosa_Behavior_Time_instant t_swap) ->
       Exists Job
         (fun j : Job =>
          Prosa_Analysis_Transform_Swap_swapped_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched t t_swap t =
          Option_some Job j)
```
