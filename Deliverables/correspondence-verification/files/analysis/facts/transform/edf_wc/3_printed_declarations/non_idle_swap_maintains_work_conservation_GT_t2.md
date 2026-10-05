# `non_idle_swap_maintains_work_conservation_GT_t2`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_GT_t2`
- Lean: `Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_GT_t2`
- Certificate: `non_idle_swap_maintains_work_conservation_GT_t2_correspondence`

## Official Rocq

```coq
non_idle_swap_maintains_work_conservation_GT_t2 :
forall {Job : JobType} {H : JobCost Job} {H1 : JobArrival Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t1 t2 : instant),
is_true (t1 <= t2) ->
forall j1 j2 : Equality.sort Job,
is_true (@scheduled_at Job (processor_state Job) sched j1 t1) ->
is_true (@scheduled_at Job (processor_state Job) sched j2 t2) ->
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true
  (@backlogged Job (processor_state Job) H H1 (@basic_ready_instance Job (processor_state Job) H1 H)
     (@swapped Job (processor_state Job) sched t1 t2) j t) ->
@work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
  arr_seq sched ->
is_true (t2 < t) ->
exists j_other : Equality.sort Job,
  is_true
    (@scheduled_at Job (processor_state Job) (@swapped Job (processor_state Job) sched t1 t2) j_other t)

non_idle_swap_maintains_work_conservation_GT_t2 is not universe polymorphic
Arguments non_idle_swap_maintains_work_conservation_GT_t2 {Job H H1} arr_seq sched 
  t1 t2 H_well_ordered j1 j2 H_t1_not_idle H_t2_not_idle j t H_arrival_j H_backlogged_j_t 
  _ _
non_idle_swap_maintains_work_conservation_GT_t2 is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_GT_t2
Declared in library prosa.analysis.facts.transform.edf_wc, line 120, characters 8-55
@non_idle_swap_maintains_work_conservation_GT_t2
     : forall (Job : JobType) (H : JobCost Job) (H1 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       forall j1 j2 : Equality.sort Job,
       is_true (@scheduled_at Job (processor_state Job) sched j1 t1) ->
       is_true (@scheduled_at Job (processor_state Job) sched j2 t2) ->
       forall (j : Equality.sort Job) (t : instant),
       @arrives_in Job arr_seq j ->
       is_true
         (@backlogged Job (processor_state Job) H H1 (@basic_ready_instance Job (processor_state Job) H1 H)
            (@swapped Job (processor_state Job) sched t1 t2) j t) ->
       @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
         arr_seq sched ->
       is_true (t2 < t) ->
       exists j_other : Equality.sort Job,
         is_true
           (@scheduled_at Job (processor_state Job) (@swapped Job (processor_state Job) sched t1 t2) j_other
              t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_GT_t2 : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    ∀ (j1 j2 : Job),
      Prosa.Behavior.Service.scheduled_at sched j1 t1 = true →
        Prosa.Behavior.Service.scheduled_at sched j2 t2 = true →
          ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
              Prosa.Behavior.Ready.backlogged (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t = true →
                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                  t2 < t →
                    ∃ j_other,
                      Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j_other
                          t =
                        true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfWc_non_idle_swap_maintains_work_conservation_GT_t2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       forall j1 j2 : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j1 t1)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j2 t2)
         Bool_true ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Behavior_Ready_backlogged_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_6
            inst_9
            (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               inst_9
               inst_6)
            (Prosa_Analysis_Transform_Swap_swapped_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               sched t1 t2)
            j t)
         Bool_true ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_3
         inst_9
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_9
            inst_6)
         arr_seq sched ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t2 t ->
       Exists Job
         (fun j_other : Job =>
          Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_Swap_swapped_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               sched t1 t2)
            j_other t =
          Bool_true)
```
