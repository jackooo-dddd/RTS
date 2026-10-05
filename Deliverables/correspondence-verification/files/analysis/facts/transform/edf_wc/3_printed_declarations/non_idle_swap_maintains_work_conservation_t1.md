# `non_idle_swap_maintains_work_conservation_t1`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t1`
- Lean: `Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_t1`
- Certificate: `non_idle_swap_maintains_work_conservation_t1_correspondence`

## Official Rocq

```coq
non_idle_swap_maintains_work_conservation_t1 :
forall {Job : JobType} {H : JobCost Job} {H1 : JobArrival Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t1 t2 : instant) (j2 : Equality.sort Job),
is_true (@scheduled_at Job (processor_state Job) sched j2 t2) ->
forall t : instant,
@work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
  arr_seq sched ->
t = t1 ->
exists j_other : Equality.sort Job,
  is_true
    (@scheduled_at Job (processor_state Job) (@swapped Job (processor_state Job) sched t1 t2) j_other t)

non_idle_swap_maintains_work_conservation_t1 is not universe polymorphic
Arguments non_idle_swap_maintains_work_conservation_t1 {Job H H1} arr_seq sched t1 t2 j2 H_t2_not_idle t _ _
non_idle_swap_maintains_work_conservation_t1 is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t1
Declared in library prosa.analysis.facts.transform.edf_wc, line 82, characters 8-52
@non_idle_swap_maintains_work_conservation_t1
     : forall (Job : JobType) (H : JobCost Job) (H1 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (t1 t2 : instant) (j2 : Equality.sort Job),
       is_true (@scheduled_at Job (processor_state Job) sched j2 t2) ->
       forall t : instant,
       @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
         arr_seq sched ->
       t = t1 ->
       exists j_other : Equality.sort Job,
         is_true
           (@scheduled_at Job (processor_state Job) (@swapped Job (processor_state Job) sched t1 t2) j_other
              t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_t1 : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t1 t2 : Prosa.Behavior.Time.instant) (j2 : Job),
  Prosa.Behavior.Service.scheduled_at sched j2 t2 = true →
    ∀ (t : Prosa.Behavior.Time.instant),
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
        t = t1 →
          ∃ j_other,
            Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j_other t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfWc_non_idle_swap_maintains_work_conservation_t1
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
         (t1 t2 : Prosa_Behavior_Time_instant) (j2 : Job),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j2 t2)
         Bool_true ->
       forall t : Prosa_Behavior_Time_instant,
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
       @eq Prosa_Behavior_Time_instant t t1 ->
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
