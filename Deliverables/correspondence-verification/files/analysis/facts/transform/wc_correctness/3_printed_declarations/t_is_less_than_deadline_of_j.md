# `t_is_less_than_deadline_of_j`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.t_is_less_than_deadline_of_j`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.t_is_less_than_deadline_of_j`
- Certificate: `t_is_less_than_deadline_of_j_correspondence`

## Official Rocq

```coq
t_is_less_than_deadline_of_j :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
  (t : instant),
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true
  (@job_ready Job (processor_state Job) H0 H (@basic.basic_ready_instance Job (processor_state Job) H H0)
     (@make_wc_at Job H H1 arr_seq sched t) j t) ->
is_true (t <= @job_deadline Job H1 j)

t_is_less_than_deadline_of_j is not universe polymorphic
Arguments t_is_less_than_deadline_of_j {Job H H0 H1} arr_seq sched t H_all_deadlines_of_arrivals_met 
  j H_arrives_in H_job_ready_sched'
t_is_less_than_deadline_of_j is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.t_is_less_than_deadline_of_j
Declared in library prosa.analysis.facts.transform.wc_correctness, line 298, characters 14-42
@t_is_less_than_deadline_of_j
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
         (t : instant),
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true
         (@job_ready Job (processor_state Job) H0 H
            (@basic.basic_ready_instance Job (processor_state Job) H H0)
            (@make_wc_at Job H H1 arr_seq sched t) j t) ->
       is_true (t <= @job_deadline Job H1 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.t_is_less_than_deadline_of_j : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Behavior.Ready.job_ready (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq sched t) j t = true →
          t ≤ Prosa.Behavior.Job.job_deadline j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_t_is_less_than_deadline_of_j
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
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_12 j)
```
