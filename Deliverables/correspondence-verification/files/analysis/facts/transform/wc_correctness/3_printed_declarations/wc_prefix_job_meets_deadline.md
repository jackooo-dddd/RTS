# `wc_prefix_job_meets_deadline`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.wc_prefix_job_meets_deadline`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_job_meets_deadline`
- Certificate: `wc_prefix_job_meets_deadline_correspondence`

## Official Rocq

```coq
wc_prefix_job_meets_deadline :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_meets_deadline Job (processor_state Job) (@wc_transform Job H H1 arr_seq sched) H0 H1 j)

wc_prefix_job_meets_deadline is not universe polymorphic
Arguments wc_prefix_job_meets_deadline {Job H H0 H1} arr_seq sched H_all_deadlines_of_arrivals_met 
  j H_arrives_in
wc_prefix_job_meets_deadline is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.wc_prefix_job_meets_deadline
Declared in library prosa.analysis.facts.transform.wc_correctness, line 517, characters 12-40
@wc_prefix_job_meets_deadline
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_meets_deadline Job (processor_state Job) (@wc_transform Job H H1 arr_seq sched) H0 H1 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_job_meets_deadline : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Behavior.Service.job_meets_deadline (Prosa.Analysis.Transform.WcTrans.wc_transform arr_seq sched) j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_wc_prefix_job_meets_deadline
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
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
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
         (Prosa_Behavior_Service_job_meets_deadline_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_WcTrans_wc_transform Job
               inst_3
               inst_6
               inst_12 arr_seq
               sched)
            inst_9
            inst_12 j)
         Bool_true
```
