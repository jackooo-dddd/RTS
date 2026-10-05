# `total_workload_shorten_range`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.total_workload_shorten_range`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.total_workload_shorten_range`
- Certificate: `total_workload_shorten_range_correspondence`

## Official Rocq

```coq
total_workload_shorten_range :
forall {Task : TaskType} {H3 : PriorityPoint Task} {Job : JobType} {H4 : JobTask Job Task}
  {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall (tsk : Equality.sort Task) (FP : FP_policy Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H4 tsk j) ->
forall (t1 : instant) (Δ : duration) (tsk_o : Equality.sort Task),
is_true (@ep_task_intf_interval Task H3 tsk tsk_o (@job_arrival Job Arrival j - t1)%N <= Δ%:R)%R ->
is_true
  (@workload_of_jobs Job Cost
     [eta (fun (tsk0 : Equality.sort Task) (jo : Equality.sort Job) =>
           @hep_job Job (@ELF Task H3 Job Arrival H4 FP) jo j &&
           @ep_task Task FP (@job_task Job Task H4 jo) (@job_task Job Task H4 j) &&
           (@job_task Job Task H4 jo == tsk0)) tsk_o]
     (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
   @workload_of_jobs Job Cost
     [eta (fun (tsk0 : Equality.sort Task) (jo : Equality.sort Job) =>
           @hep_job Job (@ELF Task H3 Job Arrival H4 FP) jo j &&
           @ep_task Task FP (@job_task Job Task H4 jo) (@job_task Job Task H4 j) &&
           (@job_task Job Task H4 jo == tsk0)) tsk_o]
     (@arrivals_between Job arr_seq t1
        `|Order.Def.max 0%R
            (t1%:R + @ep_task_intf_interval Task H3 tsk tsk_o (@job_arrival Job Arrival j - t1)%N)%R|))

total_workload_shorten_range is not universe polymorphic
Arguments total_workload_shorten_range {Task H3 Job H4 Arrival Cost} arr_seq H_valid_arrival_sequence 
  tsk FP j H_job_of_task t1 Δ tsk_o H_Δ_ge
total_workload_shorten_range is opaque
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.total_workload_shorten_range
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 424, characters 12-40
@total_workload_shorten_range
     : forall (Task : TaskType) (H3 : PriorityPoint Task) (Job : JobType) (H4 : JobTask Job Task)
         (Arrival : JobArrival Job) (Cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (tsk : Equality.sort Task) (FP : FP_policy Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H4 tsk j) ->
       forall (t1 : instant) (Δ : duration) (tsk_o : Equality.sort Task),
       is_true (@ep_task_intf_interval Task H3 tsk tsk_o (@job_arrival Job Arrival j - t1)%N <= Δ%:R)%R ->
       is_true
         (@workload_of_jobs Job Cost
            (fun x : Equality.sort Job =>
             @hep_job Job (@ELF Task H3 Job Arrival H4 FP) x j &&
             @ep_task Task FP (@job_task Job Task H4 x) (@job_task Job Task H4 j) &&
             (@job_task Job Task H4 x == tsk_o))
            (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
          @workload_of_jobs Job Cost
            (fun x : Equality.sort Job =>
             @hep_job Job (@ELF Task H3 Job Arrival H4 FP) x j &&
             @ep_task Task FP (@job_task Job Task H4 x) (@job_task Job Task H4 j) &&
             (@job_task Job Task H4 x == tsk_o))
            (@arrivals_between Job arr_seq t1
               `|Order.Def.max 0%R
                   (t1%:R + @ep_task_intf_interval Task H3 tsk tsk_o (@job_arrival Job Arrival j - t1)%N)%R|))
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.total_workload_shorten_range : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (j : Job),
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        ∀ (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration) (tsk_o : Task),
          decide
                (Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval tsk tsk_o
                    (Prosa.Behavior.Job.job_arrival j - t1) ≤
                  ↑Δ) =
              true →
            Prosa.Model.Aggregate.Workload.workload_of_jobs
                (fun x =>
                  Prosa.Model.Priority.Definitions.hep_job x j &&
                      Prosa.Model.Priority.Definitions.ep_task (Prosa.Model.Task.Concept.job_task x)
                        (Prosa.Model.Task.Concept.job_task j) &&
                    decide (Prosa.Model.Task.Concept.job_task x = tsk_o))
                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) ≤
              Prosa.Model.Aggregate.Workload.workload_of_jobs
                (fun x =>
                  Prosa.Model.Priority.Definitions.hep_job x j &&
                      Prosa.Model.Priority.Definitions.ep_task (Prosa.Model.Task.Concept.job_task x)
                        (Prosa.Model.Task.Concept.job_task j) &&
                    decide (Prosa.Model.Task.Concept.job_task x = tsk_o))
                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1
                  (max 0
                      (↑t1 +
                        Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval tsk tsk_o
                          (Prosa.Behavior.Job.job_arrival j - t1))).natAbs)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_total_workload_shorten_range
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_17 arr_seq ->
       forall (tsk : Task)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       forall (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration) (tsk_o : Task),
       @eq Bool
         (Decidable_decide
            (LE_le_inst1 Int Int_instLEInt
               (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                  inst_3
                  inst_10 tsk tsk_o
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_7
                        inst_17 j)
                     t1))
               (Nat_cast_inst1 Int instNatCastInt _UU0394_))
            (Int_decLe
               (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                  inst_3
                  inst_10 tsk tsk_o
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_7
                        inst_17 j)
                     t1))
               (Nat_cast_inst1 Int instNatCastInt _UU0394_)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_20
            (fun x : Job =>
             Bool_and
               (Bool_and
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_7
                     (Prosa_Model_Priority_Elf_ELF Task
                        inst_3
                        inst_10 Job
                        inst_7
                        inst_17
                        inst_13 FP)
                     x j)
                  (Prosa_Model_Priority_Definitions_ep_task Task
                     inst_3 FP
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 x)
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 j)))
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 x)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 x)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_)))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_20
            (fun x : Job =>
             Bool_and
               (Bool_and
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_7
                     (Prosa_Model_Priority_Elf_ELF Task
                        inst_3
                        inst_10 Job
                        inst_7
                        inst_17
                        inst_13 FP)
                     x j)
                  (Prosa_Model_Priority_Definitions_ep_task Task
                     inst_3 FP
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 x)
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 j)))
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 x)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_13 x)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1
               (Int_natAbs
                  (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                     (HAdd_hAdd_inst7 Int Int Int (instHAdd_inst1 Int Int_instAdd)
                        (Nat_cast_inst1 Int instNatCastInt t1)
                        (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                           inst_3
                           inst_10 tsk
                           tsk_o
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                              Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_7
                                 inst_17
                                 j)
                              t1)))))))
```
