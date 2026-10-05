# `no_priority_inversion`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.no_priority_inversion`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.no_priority_inversion`
- Certificate: `no_priority_inversion_correspondence`

## Official Rocq

```coq
no_priority_inversion :
forall {Task : TaskType} {Job : JobType} {H2 : JobTask Job Task} {H3 : JobArrival Job} 
  {H4 : JobCost Job} {H5 : JobPreemptable Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
forall (tsk : Equality.sort Task) (sched : @schedule Job (ideal.processor_state Job)),
@valid_schedule Job H3 (ideal.processor_state Job) sched H4
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
@valid_preemption_model Job H4 H5 (ideal.processor_state Job) arr_seq sched ->
@priority_driven.respects_JLFP_policy_at_preemption_point Job H3 H4 (ideal.processor_state Job) H5
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched 
  (@fifo.FIFO Job H3) ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H2 tsk j) ->
is_true (@job_cost_positive Job H4 j) ->
forall t1 t2 : duration,
@definitions.busy_interval Job H3 H4 (ideal.processor_state Job) sched
  (@ideal_jlfp_interference Job H3 arr_seq sched) (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched)
  j t1 t2 ->
forall Δ : duration,
is_true (t1 + Δ < t2) ->
@cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched (@fifo.FIFO Job H3) j t1
  (t1 + Δ) =
0

no_priority_inversion is not universe polymorphic
Arguments no_priority_inversion {Task Job H2 H3 H4 H5} arr_seq H_valid_arrival_sequence 
  tsk sched H_valid_schedule H_valid_preemption_model H_respects_policy_at_preemption_point 
  j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval Δ H_Δ_in_busy
no_priority_inversion is opaque
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.no_priority_inversion
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 261, characters 10-31
@no_priority_inversion
     : forall (Task : TaskType) (Job : JobType) (H2 : JobTask Job Task) (H3 : JobArrival Job)
         (H4 : JobCost Job) (H5 : JobPreemptable Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       forall (tsk : Equality.sort Task) (sched : @schedule Job (ideal.processor_state Job)),
       @valid_schedule Job H3 (ideal.processor_state Job) sched H4
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
       @valid_preemption_model Job H4 H5 (ideal.processor_state Job) arr_seq sched ->
       @priority_driven.respects_JLFP_policy_at_preemption_point Job H3 H4 (ideal.processor_state Job) H5
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched
         (@fifo.FIFO Job H3) ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H2 tsk j) ->
       is_true (@job_cost_positive Job H4 j) ->
       forall t1 t2 : duration,
       @definitions.busy_interval Job H3 H4 (ideal.processor_state Job) sched
         (@ideal_jlfp_interference Job H3 arr_seq sched)
         (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched) j t1 t2 ->
       forall Δ : duration,
       is_true (t1 + Δ < t2) ->
       @cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched 
         (@fifo.FIFO Job H3) j t1 (t1 + Δ) =
       0
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.no_priority_inversion : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] [inst_5 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
          Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
              (Prosa.Model.Priority.Fifo.FIFO Job) →
            ∀ (j : Job),
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                Prosa.Model.Task.Concept.job_of_task tsk j = true →
                  Prosa.Model.Job.Properties.job_cost_positive j = true →
                    ∀ (t1 t2 : Prosa.Behavior.Time.duration),
                      Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                        ∀ (Δ : Prosa.Behavior.Time.duration),
                          t1 + Δ < t2 →
                            Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion arr_seq sched j
                                t1 (t1 + Δ) =
                              0
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_no_priority_inversion
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_20 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall (tsk : Task)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_7)),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_14
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_17
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_14
            inst_17)
         arr_seq ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_7
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_7
         inst_14
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_20
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_14
            inst_17)
         arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_7
            inst_14) ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_17 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_interval_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_14))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_17 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_14))
         inst_14
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1 _UU0394_)
         t2 ->
       @eq Nat
         (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_14)
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
               _UU0394_))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
