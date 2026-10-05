# `basic_readiness_is_work_bearing_readiness`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.readiness.basic.basic_readiness_is_work_bearing_readiness`
- Lean: `Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_is_work_bearing_readiness`
- Certificate: `basic_readiness_is_work_bearing_readiness_correspondence`

## Official Rocq

```coq
basic_readiness_is_work_bearing_readiness :
forall {Job : JobType} {PState : ProcessorState Job} {H : JobArrival Job} {H0 : JobCost Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@work_bearing_readiness Job H H0 PState (@basic_ready_instance Job PState H H0) arr_seq sched JLFP

basic_readiness_is_work_bearing_readiness is not universe polymorphic
Arguments basic_readiness_is_work_bearing_readiness {Job PState H H0} arr_seq sched 
  {JLFP} H_priority_is_reflexive j t _ _
basic_readiness_is_work_bearing_readiness is opaque
Expands to: Constant prosa.analysis.facts.readiness.basic.basic_readiness_is_work_bearing_readiness
Declared in library prosa.analysis.facts.readiness.basic, line 62, characters 7-48
@basic_readiness_is_work_bearing_readiness
     : forall (Job : JobType) (PState : ProcessorState Job) (H : JobArrival Job) 
         (H0 : JobCost Job) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
         (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       @work_bearing_readiness Job H H0 PState (@basic_ready_instance Job PState H H0) arr_seq sched JLFP
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_is_work_bearing_readiness : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Basic_basic_readiness_is_work_bearing_readiness
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_8 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_11 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_8
         inst_11 PState
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_8
            inst_11)
         arr_seq sched JLFP
```
