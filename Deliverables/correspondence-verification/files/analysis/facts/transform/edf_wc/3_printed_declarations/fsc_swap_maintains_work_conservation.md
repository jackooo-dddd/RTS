# `fsc_swap_maintains_work_conservation`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.transform.edf_wc.fsc_swap_maintains_work_conservation`
- Lean: `Prosa.Analysis.Facts.Transform.EdfWc.fsc_swap_maintains_work_conservation`
- Certificate: `fsc_swap_maintains_work_conservation_correspondence`

## Official Rocq

```coq
fsc_swap_maintains_work_conservation :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (processor_state Job) sched ->
@completed_jobs_dont_execute Job (processor_state Job) sched H ->
@jobs_come_from_arrival_sequence Job (processor_state Job) sched arr_seq ->
forall (j1 : Equality.sort Job) (t1 : instant),
is_true (@scheduled_at Job (processor_state Job) sched j1 t1) ->
is_true (t1 < @job_deadline Job H0 j1) ->
@work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
  arr_seq sched ->
@work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
  arr_seq
  (@swapped Job (processor_state Job) sched t1 (@edf_trans.find_swap_candidate Job H0 H1 sched t1 j1))

fsc_swap_maintains_work_conservation is not universe polymorphic
Arguments fsc_swap_maintains_work_conservation {Job H H0 H1} arr_seq sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_from_arr_seq j1 t1 H_not_idle H_deadline_not_missed 
  _ j t _ _
fsc_swap_maintains_work_conservation is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_wc.fsc_swap_maintains_work_conservation
Declared in library prosa.analysis.facts.transform.edf_wc, line 209, characters 12-48
@fsc_swap_maintains_work_conservation
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (processor_state Job) sched ->
       @completed_jobs_dont_execute Job (processor_state Job) sched H ->
       @jobs_come_from_arrival_sequence Job (processor_state Job) sched arr_seq ->
       forall (j1 : Equality.sort Job) (t1 : instant),
       is_true (@scheduled_at Job (processor_state Job) sched j1 t1) ->
       is_true (t1 < @job_deadline Job H0 j1) ->
       @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
         arr_seq sched ->
       @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
         arr_seq
         (@swapped Job (processor_state Job) sched t1 (@edf_trans.find_swap_candidate Job H0 H1 sched t1 j1))
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfWc.fsc_swap_maintains_work_conservation : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        ∀ (j1 : Job) (t1 : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Service.scheduled_at sched j1 t1 = true →
            t1 < Prosa.Behavior.Job.job_deadline j1 →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq
                  (Prosa.Analysis.Transform.Swap.swapped sched t1
                    (Prosa.Analysis.Transform.EdfTrans.find_swap_candidate sched t1 j1))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfWc_fsc_swap_maintains_work_conservation
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched inst_6 ->
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched arr_seq ->
       forall (j1 : Job) (t1 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j1 t1)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j1) ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_3
         inst_12
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_12
            inst_6)
         arr_seq sched ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_3
         inst_12
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_12
            inst_6)
         arr_seq
         (Prosa_Analysis_Transform_Swap_swapped_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched t1
            (Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job
               inst_3
               inst_9
               inst_12 sched t1 j1))
```
