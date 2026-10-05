# `wc_transform_correctness`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.facts.transform.wc_correctness.wc_transform_correctness`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_correctness`
- Certificate: `wc_transform_correctness_correspondence`

## Official Rocq

```coq
wc_transform_correctness :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H (processor_state Job) sched H0
  (@basic.basic_ready_instance Job (processor_state Job) H H0) arr_seq ->
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
@valid_schedule Job H (processor_state Job) (@wc_transform Job H H1 arr_seq sched) H0
  (@basic.basic_ready_instance Job (processor_state Job) H H0) arr_seq /\
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq (@wc_transform Job H H1 arr_seq sched) /\
@work_conserving Job H H0 (processor_state Job) (@basic.basic_ready_instance Job (processor_state Job) H H0)
  arr_seq (@wc_transform Job H H1 arr_seq sched)

wc_transform_correctness is not universe polymorphic
Arguments wc_transform_correctness {Job H H0 H1} arr_seq H_arr_seq_valid sched H_sched_valid
  H_all_deadlines_of_arrivals_met
wc_transform_correctness is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.wc_transform_correctness
Declared in library prosa.analysis.facts.transform.wc_correctness, line 677, characters 10-34
@wc_transform_correctness
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H (processor_state Job) sched H0
         (@basic.basic_ready_instance Job (processor_state Job) H H0) arr_seq ->
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
       @valid_schedule Job H (processor_state Job) (@wc_transform Job H H1 arr_seq sched) H0
         (@basic.basic_ready_instance Job (processor_state Job) H H0) arr_seq /\
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq
         (@wc_transform Job H H1 arr_seq sched) /\
       @work_conserving Job H H0 (processor_state Job)
         (@basic.basic_ready_instance Job (processor_state Job) H H0) arr_seq
         (@wc_transform Job H H1 arr_seq sched)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_correctness : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
          Prosa.Behavior.Ready.valid_schedule (Prosa.Analysis.Transform.WcTrans.wc_transform arr_seq sched) arr_seq ∧
            Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq
                (Prosa.Analysis.Transform.WcTrans.wc_transform arr_seq sched) ∧
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq
                (Prosa.Analysis.Transform.WcTrans.wc_transform arr_seq sched)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_wc_transform_correctness
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
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_6
            inst_9)
         arr_seq ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq sched ->
       And
         (Prosa_Behavior_Ready_valid_schedule_inst4 Job
            inst_3
            inst_6
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_WcTrans_wc_transform Job
               inst_3
               inst_6
               inst_12 arr_seq
               sched)
            inst_9
            (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               inst_6
               inst_9)
            arr_seq)
         (And
            (Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
               inst_3
               inst_9
               inst_12
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               arr_seq
               (Prosa_Analysis_Transform_WcTrans_wc_transform Job
                  inst_3
                  inst_6
                  inst_12 arr_seq
                  sched))
            (Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
               inst_3
               inst_6
               inst_9
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  inst_6
                  inst_9)
               arr_seq
               (Prosa_Analysis_Transform_WcTrans_wc_transform Job
                  inst_3
                  inst_6
                  inst_12 arr_seq
                  sched)))
```
