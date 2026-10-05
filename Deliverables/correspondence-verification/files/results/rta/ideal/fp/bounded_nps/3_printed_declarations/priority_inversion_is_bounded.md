# `priority_inversion_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded`
- Lean: `Prosa.Results.Rta.Ideal.Fp.BoundedNps.priority_inversion_is_bounded`
- Certificate: `priority_inversion_is_bounded_correspondence`

## Official Rocq

```coq
priority_inversion_is_bounded :
forall {Task : TaskType} {H1 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} 
  {H2 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job} {FP : FP_policy Task},
@transitive_task_priorities Task FP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job Arrival arr_seq ->
forall (sched : @schedule Job (ideal.processor_state Job))
  {H3 : @JobReady Job (ideal.processor_state Job) Cost Arrival},
@work_bearing_readiness Job Arrival Cost (ideal.processor_state Job) H3 arr_seq sched
  (@FP_to_JLFP Job Task H2 FP) ->
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost H3 arr_seq ->
forall {H4 : JobPreemptable Job},
@valid_model_with_bounded_nonpreemptive_segments Task Job H2 Cost H1 H4 (ideal.processor_state Job) arr_seq
  sched ->
@respects_FP_policy_at_preemption_point Task Job H2 Arrival Cost (ideal.processor_state Job) H4 H3 arr_seq
  sched FP ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
forall tsk : Equality.sort Task,
@valid_preemption_model Job Cost H4 (ideal.processor_state Job) arr_seq sched ->
@priority_inversion_is_bounded_by Task Job H2 Arrival Cost (ideal.processor_state Job) arr_seq sched
  (@FP_to_JLFP Job Task H2 FP) tsk (@constant duration nat (@blocking_bound Task H1 FP ts tsk))

priority_inversion_is_bounded is not universe polymorphic
Arguments priority_inversion_is_bounded {Task H1 Job H2 Arrival Cost FP} H_priority_is_transitive 
  arr_seq H_valid_arrival_sequence sched {H3} H_job_ready H_sched_valid {H4}
  H_valid_model_with_bounded_nonpreemptive_segments H_respects_policy ts%seq_scope 
  H_all_jobs_from_taskset tsk H_valid_preemption_model j _ _ _ t1 t2 _
priority_inversion_is_bounded is opaque
Expands to: Constant prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded
Declared in library prosa.results.rta.ideal.fp.bounded_nps, line 144, characters 8-37
@priority_inversion_is_bounded
     : forall (Task : TaskType) (H1 : TaskMaxNonpreemptiveSegment Task) (Job : JobType)
         (H2 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job) 
         (FP : FP_policy Task),
       @transitive_task_priorities Task FP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (sched : @schedule Job (ideal.processor_state Job))
         (H3 : @JobReady Job (ideal.processor_state Job) Cost Arrival),
       @work_bearing_readiness Job Arrival Cost (ideal.processor_state Job) H3 arr_seq sched
         (@FP_to_JLFP Job Task H2 FP) ->
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost H3 arr_seq ->
       forall H4 : JobPreemptable Job,
       @valid_model_with_bounded_nonpreemptive_segments Task Job H2 Cost H1 H4 (ideal.processor_state Job)
         arr_seq sched ->
       @respects_FP_policy_at_preemption_point Task Job H2 Arrival Cost (ideal.processor_state Job) H4 H3
         arr_seq sched FP ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       forall tsk : Equality.sort Task,
       @valid_preemption_model Job Cost H4 (ideal.processor_state Job) arr_seq sched ->
       @priority_inversion_is_bounded_by Task Job H2 Arrival Cost (ideal.processor_state Job) arr_seq sched
         (@FP_to_JLFP Job Task H2 FP) tsk (@constant duration nat (@blocking_bound Task H1 FP ts tsk))
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.BoundedNps.priority_inversion_is_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [FP : Prosa.Model.Priority.Definitions.FP_policy Task],
  Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
          [inst_6 : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
          Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              ∀ [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
                  Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched FP →
                    ∀ (ts : List Task),
                      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                        ∀ (tsk : Task),
                          Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                            Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq sched
                              tsk
                              (Prosa.Util.Notation.constant
                                (Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk))
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_BoundedNps_priority_inversion_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_17 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_7))
         (inst_44 : 
          Prosa_Behavior_Ready_JobReady_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_20
            inst_17),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4 Job
         inst_7
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_44 arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_13 FP) ->
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_20
         inst_44 arr_seq ->
       forall
         inst_70 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7,
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments_inst8 Task
         inst_3 Job
         inst_7
         inst_13
         inst_20
         inst_10
         inst_70
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst8 Task
         inst_3 Job
         inst_7
         inst_13
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_70
         inst_44 arr_seq sched FP ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_13 arr_seq ts ->
       forall tsk : Task,
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_7
         inst_20
         inst_70
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_13
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_13 FP)
         tsk
         (Prosa_Util_Notation_constant_inst3 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
               inst_3
               inst_10 FP ts tsk))
```
