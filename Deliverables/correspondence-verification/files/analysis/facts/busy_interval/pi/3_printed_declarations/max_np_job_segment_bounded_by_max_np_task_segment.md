# `max_np_job_segment_bounded_by_max_np_task_segment`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi.max_np_job_segment_bounded_by_max_np_task_segment`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.max_np_job_segment_bounded_by_max_np_task_segment`
- Certificate: `max_np_job_segment_bounded_by_max_np_task_segment_correspondence`

## Official Rocq

```coq
max_np_job_segment_bounded_by_max_np_task_segment :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H2 : JobCost Job}
  (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : @schedule Job PState)
  {JLFP : JLFP_policy Job} {H3 : TaskMaxNonpreemptiveSegment Task} {H4 : JobPreemptable Job}
  (j : Equality.sort Job) (t1 : instant),
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
is_true
  (@max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1 <=
   \max_(j_lp <- @arrivals_between Job arr_seq 0 t1 | ~~ @hep_job Job JLFP j_lp j &&
                                                      (0 < @job_cost Job H2 j_lp))
      (@task_max_nonpreemptive_segment Task H3 (@job_task Job Task H0 j_lp) - 1))

max_np_job_segment_bounded_by_max_np_task_segment is not universe polymorphic
Arguments max_np_job_segment_bounded_by_max_np_task_segment {Task Job H0 H2} arr_seq 
  {PState} sched {JLFP H3 H4} j t1 H_valid_nps
max_np_job_segment_bounded_by_max_np_task_segment is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi.max_np_job_segment_bounded_by_max_np_task_segment
Declared in library prosa.analysis.facts.busy_interval.pi, line 343, characters 10-59
@max_np_job_segment_bounded_by_max_np_task_segment
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H2 : JobCost Job)
         (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (JLFP : JLFP_policy Job) (H3 : TaskMaxNonpreemptiveSegment Task) (H4 : JobPreemptable Job)
         (j : Equality.sort Job) (t1 : instant),
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
       is_true
         (@max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1 <=
          \max_(j_lp <- @arrivals_between Job arr_seq 0 t1 | ~~ @hep_job Job JLFP j_lp j &&
                                                             (0 < @job_cost Job H2 j_lp))
             (@task_max_nonpreemptive_segment Task H3 (@job_task Job Task H0 j_lp) - 1))
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.max_np_job_segment_bounded_by_max_np_task_segment : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
  [inst_4 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_5 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (j : Job) (t1 : Prosa.Behavior.Time.instant),
  Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
    Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment arr_seq j t1 ≤
      Prosa.Util.Minmax.bigMaxListCond (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq 0 t1)
        (fun j_lp => !Prosa.Model.Priority.Definitions.hep_job j_lp j && decide (0 < Prosa.Behavior.Job.job_cost j_lp))
        fun j_lp =>
        Prosa.Model.Task.Preemption.Parameters.task_max_nonpreemptive_segment (Prosa.Model.Task.Concept.job_task j_lp) -
          1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_max_np_job_segment_bounded_by_max_np_task_segment
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_25 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_28 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (j : Job) (t1 : Prosa_Behavior_Time_instant),
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_10
         inst_14
         inst_25
         inst_28 PState arr_seq sched ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
            inst_3
            inst_14 arr_seq JLFP
            inst_28 j t1)
         (Prosa_Util_Minmax_bigMaxListCond Job
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t1)
            (fun j_lp : Job =>
             Bool_and
               (Bool_not
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_3 JLFP j_lp j))
               (Decidable_decide
                  (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
                     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
                     (Prosa_Behavior_Job_JobCost_job_cost Job
                        inst_3
                        inst_14 j_lp))
                  (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
                     (Prosa_Behavior_Job_JobCost_job_cost Job
                        inst_3
                        inst_14 j_lp))))
            (fun j_lp : Job =>
             HSub_hSub_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
               (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
               (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
                  Task inst_7
                  inst_25
                  (Prosa_Model_Task_Concept_JobTask_job_task Job
                     inst_3 Task
                     inst_7
                     inst_10 j_lp))
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
```
