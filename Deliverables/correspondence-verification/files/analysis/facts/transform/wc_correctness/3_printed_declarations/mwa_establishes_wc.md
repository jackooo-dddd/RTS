# `mwa_establishes_wc`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.mwa_establishes_wc`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_establishes_wc`
- Certificate: `mwa_establishes_wc_correspondence`

## Official Rocq

```coq
mwa_establishes_wc :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall (sched : @schedule Job (processor_state Job)) (t : instant),
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
(forall t_l : nat, is_true (t_l < t) -> @is_work_conserving_at Job H H0 arr_seq sched t_l) ->
forall t_l : nat,
is_true (t_l <= t) -> @is_work_conserving_at Job H H0 arr_seq (@make_wc_at Job H H1 arr_seq sched t) t_l

mwa_establishes_wc is not universe polymorphic
Arguments mwa_establishes_wc {Job H H0 H1} arr_seq H_arr_seq_valid sched t _ _%function_scope 
  t_l%nat_scope _ _
mwa_establishes_wc is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.mwa_establishes_wc
Declared in library prosa.analysis.facts.transform.wc_correctness, line 373, characters 10-28
@mwa_establishes_wc
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall (sched : @schedule Job (processor_state Job)) (t : instant),
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
       (forall t_l : nat, is_true (t_l < t) -> @is_work_conserving_at Job H H0 arr_seq sched t_l) ->
       forall t_l : nat,
       is_true (t_l <= t) ->
       @is_work_conserving_at Job H H0 arr_seq (@make_wc_at Job H H1 arr_seq sched t) t_l
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_establishes_wc : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
      (t : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
        (∀ t_l < t, Prosa.Analysis.Facts.Transform.WcCorrectness.is_work_conserving_at arr_seq sched t_l) →
          ∀ t_l ≤ t,
            Prosa.Analysis.Facts.Transform.WcCorrectness.is_work_conserving_at arr_seq
              (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq sched t) t_l
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_establishes_wc
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
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
       (forall t_l : Nat,
        LT_lt_inst1 Nat instLTNat t_l t ->
        Prosa_Analysis_Facts_Transform_WcCorrectness_is_work_conserving_at Job
          inst_3
          inst_6
          inst_9 arr_seq sched t_l) ->
       forall t_l : Nat,
       LE_le_inst1 Nat instLENat t_l t ->
       Prosa_Analysis_Facts_Transform_WcCorrectness_is_work_conserving_at Job
         inst_3
         inst_6
         inst_9 arr_seq
         (Prosa_Analysis_Transform_WcTrans_make_wc_at Job
            inst_3
            inst_6
            inst_12 arr_seq sched t)
         t_l
```
