# `overheads_sbf_busy_valid`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_busy_valid`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.overheads_sbf_busy_valid`
- Certificate: `overheads_sbf_busy_valid_correspondence`

## Official Rocq

```coq
overheads_sbf_busy_valid :
forall {Task : TaskType} {H : MaxArrivals Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} {H3 : JobPreemptable Job} {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H1 (processor_state Job) sched H2 (@basic_ready_instance Job (processor_state Job) H1 H2)
  arr_seq ->
@work_conserving Job H1 H2 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H2)
  arr_seq sched ->
@no_superfluous_preemptions Job H2 (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H0 FP)) 
  (processor_state Job) sched ->
@respects_FP_policy_at_preemption_point Task Job H0 H1 H2 (processor_state Job) H3
  (@basic_ready_instance Job (processor_state Job) H1 H2) arr_seq sched FP ->
@valid_preemption_model Job H2 H3 (processor_state Job) arr_seq sched ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H0 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H0 arr_seq H ts ->
(forall j : Equality.sort Job, @arrives_in Job arr_seq j -> is_true (@job_cost_positive Job H2 j)) ->
forall DB CSB CRPDB : duration,
@overhead_resource_model Job sched DB CSB CRPDB ->
forall tsk : Equality.sort Task,
@valid_busy_sbf Task Job H1 H2 H0 (processor_state Job) arr_seq sched (@FP_to_JLFP Job Task H0 FP) tsk
  (@fp_ovh_sbf_slow Task FP H ts DB CSB CRPDB tsk)

overheads_sbf_busy_valid is not universe polymorphic
Arguments overheads_sbf_busy_valid {Task H Job H0 H1 H2 H3 FP} H_priority_is_reflexive
  H_priority_is_transitive arr_seq H_valid_arrival_sequence sched H_valid_schedule 
  H_work_conserving H_no_superfluous_preemptions H_respects_policy H_valid_preemption_model 
  ts%seq_scope H_all_jobs_from_taskset H_is_arrival_curve H_all_jobs_have_positive_cost%function_scope 
  DB CSB CRPDB H_valid_overheads_model tsk
overheads_sbf_busy_valid is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_busy_valid
Declared in library prosa.analysis.facts.model.overheads.sbf.fp, line 186, characters 8-32
@overheads_sbf_busy_valid
     : forall (Task : TaskType) (H : MaxArrivals Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (H3 : JobPreemptable Job) (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H1 (processor_state Job) sched H2
         (@basic_ready_instance Job (processor_state Job) H1 H2) arr_seq ->
       @work_conserving Job H1 H2 (processor_state Job)
         (@basic_ready_instance Job (processor_state Job) H1 H2) arr_seq sched ->
       @no_superfluous_preemptions Job H2 (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H0 FP))
         (processor_state Job) sched ->
       @respects_FP_policy_at_preemption_point Task Job H0 H1 H2 (processor_state Job) H3
         (@basic_ready_instance Job (processor_state Job) H1 H2) arr_seq sched FP ->
       @valid_preemption_model Job H2 H3 (processor_state Job) arr_seq sched ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H0 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H0 arr_seq H ts ->
       (forall j : Equality.sort Job, @arrives_in Job arr_seq j -> is_true (@job_cost_positive Job H2 j)) ->
       forall DB CSB CRPDB : duration,
       @overhead_resource_model Job sched DB CSB CRPDB ->
       forall tsk : Equality.sort Task,
       @valid_busy_sbf Task Job H1 H2 H0 (processor_state Job) arr_seq sched (@FP_to_JLFP Job Task H0 FP) tsk
         (@fp_ovh_sbf_slow Task FP H ts DB CSB CRPDB tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.overheads_sbf_busy_valid : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                Prosa.Model.Preemption.Parameter.no_superfluous_preemptions sched →
                  Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched FP →
                    Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                      ∀ (ts : List Task),
                        Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                            (∀ (j : Job),
                                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                  Prosa.Model.Job.Properties.job_cost_positive j = true) →
                              ∀ (DB CSB CRPDB : Prosa.Behavior.Time.duration),
                                Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model sched DB CSB CRPDB →
                                  ∀ (tsk : Task),
                                    Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf arr_seq sched tsk
                                      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_overheads_sbf_busy_valid
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (inst_23 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_10)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_10,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_10
                   (Prosa_Model_Processor_Overheads_processor_state Job
                      inst_10),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_10
         inst_17
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_10)
         sched inst_20
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_10
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_10)
            inst_17
            inst_20)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_10
         inst_17
         inst_20
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_10)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_10
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_10)
            inst_17
            inst_20)
         arr_seq sched ->
       Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job
         inst_10
         inst_20
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_10
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_10 Task
               inst_3
               inst_13 FP))
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_10)
         sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst8 Task
         inst_3 Job
         inst_10
         inst_13
         inst_17
         inst_20
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_10)
         inst_23
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_10
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_10)
            inst_17
            inst_20)
         arr_seq sched FP ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_10
         inst_20
         inst_23
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_10)
         arr_seq sched ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_10
         inst_13 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq
         inst_6 ts ->
       (forall j : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_10 arr_seq j ->
        @eq Bool
          (Prosa_Model_Job_Properties_job_cost_positive Job
             inst_10
             inst_20 j)
          Bool_true) ->
       forall DB CSB CRPDB : Prosa_Behavior_Time_duration,
       Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job
         inst_10 sched DB CSB CRPDB ->
       forall tsk : Task,
       Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf_inst8 Task
         inst_3 Job
         inst_10
         inst_17
         inst_20
         inst_13
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_10)
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_10 Task
            inst_3
            inst_13 FP)
         tsk
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            (Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_ovh_sbf_slow Task
               inst_3 FP
               inst_6 ts DB CSB
               CRPDB tsk))
```
