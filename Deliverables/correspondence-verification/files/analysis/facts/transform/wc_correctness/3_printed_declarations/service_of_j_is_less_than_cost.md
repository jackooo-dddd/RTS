# `service_of_j_is_less_than_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.service_of_j_is_less_than_cost`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.service_of_j_is_less_than_cost`
- Certificate: `service_of_j_is_less_than_cost_correspondence`

## Official Rocq

```coq
service_of_j_is_less_than_cost :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
  (t : instant) (j : Equality.sort Job),
is_true
  (@job_ready Job (processor_state Job) H0 H (@basic.basic_ready_instance Job (processor_state Job) H H0)
     (@make_wc_at Job H H1 arr_seq sched t) j t) ->
is_true (@service Job (processor_state Job) sched j t < @job_cost Job H0 j)

service_of_j_is_less_than_cost is not universe polymorphic
Arguments service_of_j_is_less_than_cost {Job H H0 H1} arr_seq sched t j H_job_ready_sched'
service_of_j_is_less_than_cost is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.service_of_j_is_less_than_cost
Declared in library prosa.analysis.facts.transform.wc_correctness, line 286, characters 14-44
@service_of_j_is_less_than_cost
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
         (t : instant) (j : Equality.sort Job),
       is_true
         (@job_ready Job (processor_state Job) H0 H
            (@basic.basic_ready_instance Job (processor_state Job) H H0)
            (@make_wc_at Job H H1 arr_seq sched t) j t) ->
       is_true (@service Job (processor_state Job) sched j t < @job_cost Job H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.service_of_j_is_less_than_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant) (j : Job),
  Prosa.Behavior.Ready.job_ready (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq sched t) j t = true →
    Prosa.Behavior.Service.service sched j t < Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_service_of_j_is_less_than_cost
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
         (t : Prosa_Behavior_Time_instant) (j : Job),
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
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (Prosa_Behavior_Service_service_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j t)
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_9 j)
```
