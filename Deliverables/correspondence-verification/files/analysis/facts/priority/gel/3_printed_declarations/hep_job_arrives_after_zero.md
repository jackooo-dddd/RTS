# `hep_job_arrives_after_zero`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.priority.gel.hep_job_arrives_after_zero`
- Lean: `Prosa.Analysis.Facts.Priority.Gel.hep_job_arrives_after_zero`
- Certificate: `hep_job_arrives_after_zero_correspondence`

## Official Rocq

```coq
hep_job_arrives_after_zero :
forall {Task : concept.TaskType} {Job : job.JobType} {H : concept.JobTask Job Task}
  {H0 : gel.PriorityPoint Task} {Arrival : job.JobArrival Job} (j j' : Equality.sort Job),
is_true (@definitions.hep_job Job (@gel.GEL Job Task H0 Arrival H) j' j) ->
is_true
  (@order.Order.le ssrnum.ring_display
     (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
        ssrint.ssrint_int__canonical__Num_POrderedZmodule)
     (@ssralg.GRing.zero
        (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
           ssrint.ssrint_int__canonical__Num_POrderedZmodule))
     (@ssralg.GRing.add
        (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
           ssrint.ssrint_int__canonical__GRing_PzSemiRing)
        (@ssralg.GRing.add
           (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
              ssrint.ssrint_int__canonical__GRing_PzSemiRing)
           (@ssralg.GRing.natmul
              (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                 ssrint.ssrint_int__canonical__GRing_PzSemiRing)
              (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing)
              (@job.job_arrival Job Arrival j))
           (@gel.task_priority_point Task H0 (@concept.job_task Job Task H j)))
        (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
           (@gel.task_priority_point Task H0 (@concept.job_task Job Task H j')))))

hep_job_arrives_after_zero is not universe polymorphic
Arguments hep_job_arrives_after_zero {Task Job H H0 Arrival} j j' H_j'_hep
hep_job_arrives_after_zero is opaque
Expands to: Constant prosa.analysis.facts.priority.gel.hep_job_arrives_after_zero
Declared in library prosa.analysis.facts.priority.gel, line 53, characters 14-40
@hep_job_arrives_after_zero
     : forall (Task : concept.TaskType) (Job : job.JobType) (H : concept.JobTask Job Task)
         (H0 : gel.PriorityPoint Task) (Arrival : job.JobArrival Job) (j j' : Equality.sort Job),
       is_true (@definitions.hep_job Job (@gel.GEL Job Task H0 Arrival H) j' j) ->
       is_true
         (@order.Order.le ssrnum.ring_display
            (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
               ssrint.ssrint_int__canonical__Num_POrderedZmodule)
            (@ssralg.GRing.zero
               (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                  ssrint.ssrint_int__canonical__Num_POrderedZmodule))
            (@ssralg.GRing.add
               (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                  ssrint.ssrint_int__canonical__GRing_PzSemiRing)
               (@ssralg.GRing.add
                  (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                     ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                  (@ssralg.GRing.natmul
                     (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                        ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                     (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                     (@job.job_arrival Job Arrival j))
                  (@gel.task_priority_point Task H0 (@concept.job_task Job Task H j)))
               (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                  (@gel.task_priority_point Task H0 (@concept.job_task Job Task H j')))))
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Gel.hep_job_arrives_after_zero : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  [Arrival : Prosa.Behavior.Job.JobArrival Job] (j j' : Job),
  Prosa.Model.Priority.Definitions.hep_job j' j = true →
    decide
        (0 ≤
          ↑(Prosa.Behavior.Job.job_arrival j) +
              Prosa.Model.Priority.Gel.task_priority_point (Prosa.Model.Task.Concept.job_task j) -
            Prosa.Model.Priority.Gel.task_priority_point (Prosa.Model.Task.Concept.job_task j')) =
      true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Gel_hep_job_arrives_after_zero
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Arrival : Prosa_Behavior_Job_JobArrival Job
                      inst_7)
         (j j' : Job),
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_14 Arrival
               inst_10)
            j' j)
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (LE_le_inst1 Int Int_instLEInt (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
               (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                  (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                     (Nat_cast_inst1 Int instNatCastInt
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_7 Arrival j))
                     (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                        inst_3
                        inst_14
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_7 Task
                           inst_3
                           inst_10 j)))
                  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                     inst_3
                     inst_14
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_10 j'))))
            (Int_decLe (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
               (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                  (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                     (Nat_cast_inst1 Int instNatCastInt
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_7 Arrival j))
                     (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                        inst_3
                        inst_14
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_7 Task
                           inst_3
                           inst_10 j)))
                  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                     inst_3
                     inst_14
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_10 j')))))
         Bool_true
```
