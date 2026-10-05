# `total_ep_tsk_workload_shorten_range`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.workload.elf_athep_bound.total_ep_tsk_workload_shorten_range`
- Lean: `Prosa.Analysis.Facts.Workload.ElfAthepBound.total_ep_tsk_workload_shorten_range`
- Certificate: `total_ep_tsk_workload_shorten_range_correspondence`

## Official Rocq

```coq
total_ep_tsk_workload_shorten_range :
forall {Task : TaskType} {H1 : PriorityPoint Task} {Job : JobType} {H2 : JobTask Job Task}
  {H3 : JobArrival Job} {H4 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
forall (tsk : Equality.sort Task) (FP : FP_policy Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H2 tsk j) ->
forall (t1 delta : duration) (tsk_o : Equality.sort Task),
is_true (@ep_task_interfering_interval_length Task H1 tsk tsk_o (@job_arrival Job H3 j - t1)%N <= delta%:R)%R ->
is_true (@ep_task Task FP tsk tsk_o) ->
is_true
  (@workload_of_jobs Job H4
     ((fun (tsk_o0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o0)) tsk_o)
     (@arrivals_between Job arr_seq t1 (t1 + delta)) <=
   @workload_of_jobs Job H4
     ((fun (tsk_o0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o0)) tsk_o)
     (@arrivals_between Job arr_seq t1
        `|Order.Def.max 0%R
            (t1%:R + @ep_task_interfering_interval_length Task H1 tsk tsk_o (@job_arrival Job H3 j - t1)%N)%R|))

total_ep_tsk_workload_shorten_range is not universe polymorphic
Arguments total_ep_tsk_workload_shorten_range {Task H1 Job H2 H3 H4} arr_seq H_valid_arrival_sequence 
  tsk FP j H_job_of_tsk t1 delta tsk_o H_delta_ge _
total_ep_tsk_workload_shorten_range is opaque
Expands to: Constant prosa.analysis.facts.workload.elf_athep_bound.total_ep_tsk_workload_shorten_range
Declared in library prosa.analysis.facts.workload.elf_athep_bound, line 108, characters 12-47
@total_ep_tsk_workload_shorten_range
     : forall (Task : TaskType) (H1 : PriorityPoint Task) (Job : JobType) (H2 : JobTask Job Task)
         (H3 : JobArrival Job) (H4 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       forall (tsk : Equality.sort Task) (FP : FP_policy Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H2 tsk j) ->
       forall (t1 delta : duration) (tsk_o : Equality.sort Task),
       is_true
         (@ep_task_interfering_interval_length Task H1 tsk tsk_o (@job_arrival Job H3 j - t1)%N <= delta%:R)%R ->
       is_true (@ep_task Task FP tsk tsk_o) ->
       is_true
         (@workload_of_jobs Job H4
            (fun jo : Equality.sort Job =>
             @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o))
            (@arrivals_between Job arr_seq t1 (t1 + delta)) <=
          @workload_of_jobs Job H4
            (fun jo : Equality.sort Job =>
             @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o))
            (@arrivals_between Job arr_seq t1
               `|Order.Def.max 0%R
                   (t1%:R +
                    @ep_task_interfering_interval_length Task H1 tsk tsk_o (@job_arrival Job H3 j - t1)%N)%R|))
```

## Lean

```lean
@Prosa.Analysis.Facts.Workload.ElfAthepBound.total_ep_tsk_workload_shorten_range : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Priority.Gel.PriorityPoint Task] {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (j : Job),
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        ∀ (t1 delta : Prosa.Behavior.Time.duration) (tsk_o : Task),
          decide
                (Prosa.Analysis.Definitions.Workload.ElfAthepBound.ep_task_interfering_interval_length tsk tsk_o
                    (Prosa.Behavior.Job.job_arrival j - t1) ≤
                  ↑delta) =
              true →
            Prosa.Model.Priority.Definitions.ep_task tsk tsk_o = true →
              Prosa.Model.Aggregate.Workload.workload_of_jobs
                  (fun jo =>
                    Prosa.Model.Priority.Definitions.hep_job jo j &&
                      decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                  (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + delta)) ≤
                Prosa.Model.Aggregate.Workload.workload_of_jobs
                  (fun jo =>
                    Prosa.Model.Priority.Definitions.hep_job jo j &&
                      decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                  (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1
                    (max 0
                        (↑t1 +
                          Prosa.Analysis.Definitions.Workload.ElfAthepBound.ep_task_interfering_interval_length tsk
                            tsk_o (Prosa.Behavior.Job.job_arrival j - t1))).natAbs)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Workload_ElfAthepBound_total_ep_tsk_workload_shorten_range
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall (tsk : Task)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_10 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       forall (t1 delta : Prosa_Behavior_Time_duration) (tsk_o : Task),
       @eq Bool
         (Decidable_decide
            (LE_le_inst1 Int Int_instLEInt
               (Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length Task
                  inst_3
                  inst_6 tsk tsk_o
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_10
                        inst_17 j)
                     t1))
               (Nat_cast_inst1 Int instNatCastInt delta))
            (Int_decLe
               (Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length Task
                  inst_3
                  inst_6 tsk tsk_o
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_10
                        inst_17 j)
                     t1))
               (Nat_cast_inst1 Int instNatCastInt delta)))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_ep_task Task
            inst_3 FP tsk tsk_o)
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_10
            inst_20
            (fun jo : Job =>
             Bool_and
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_10
                  (Prosa_Model_Priority_Elf_ELF Task
                     inst_3
                     inst_6 Job
                     inst_10
                     inst_17
                     inst_13 FP)
                  jo j)
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10 Task
                        inst_3
                        inst_13 jo)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10 Task
                        inst_3
                        inst_13 jo)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_10 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                  delta)))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_10
            inst_20
            (fun jo : Job =>
             Bool_and
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_10
                  (Prosa_Model_Priority_Elf_ELF Task
                     inst_3
                     inst_6 Job
                     inst_10
                     inst_17
                     inst_13 FP)
                  jo j)
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10 Task
                        inst_3
                        inst_13 jo)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10 Task
                        inst_3
                        inst_13 jo)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_10 arr_seq t1
               (Int_natAbs
                  (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                     (HAdd_hAdd_inst7 Int Int Int (instHAdd_inst1 Int Int_instAdd)
                        (Nat_cast_inst1 Int instNatCastInt t1)
                        (Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length
                           Task
                           inst_3
                           inst_6
                           tsk tsk_o
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                              Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_10
                                 inst_17
                                 j)
                              t1)))))))
```
