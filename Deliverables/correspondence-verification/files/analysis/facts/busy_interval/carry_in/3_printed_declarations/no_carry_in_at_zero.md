# `no_carry_in_at_zero`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.carry_in.no_carry_in_at_zero`
- Lean: `Prosa.Analysis.Facts.BusyInterval.CarryIn.no_carry_in_at_zero`
- Certificate: `no_carry_in_at_zero_correspondence`

## Official Rocq

```coq
no_carry_in_at_zero :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState),
@no_carry_in Job H1 H2 arr_seq PState sched 0

no_carry_in_at_zero is not universe polymorphic
Arguments no_carry_in_at_zero {Job H1 H2} arr_seq {PState} sched j_o _ _
no_carry_in_at_zero is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.carry_in.no_carry_in_at_zero
Declared in library prosa.analysis.facts.busy_interval.carry_in, line 63, characters 8-27
@no_carry_in_at_zero
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState),
       @no_carry_in Job H1 H2 arr_seq PState sched 0
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.CarryIn.no_carry_in_at_zero : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState), Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_CarryIn_no_carry_in_at_zero
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
         inst_3
         inst_6
         inst_9 arr_seq PState sched
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
```
