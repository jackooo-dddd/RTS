import Prosa.Analysis.Abstract.Definitions
import Validation.fixtures.translation_order.ServiceComputationInterface

namespace Prosa.Validation.AbstractDefinitionsInterface

open Prosa.Analysis.Abstract.Definitions
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u

variable {Job : JobType} [DecidableEq Job]
variable [Interference Job] [InterferingWorkload Job]

/-- Source-shaped computation interface for the half-open Boolean sum.  The
whole-constant guard below ties this interface to the compiled production
definition, not to a manually substituted Rocq model. -/
noncomputable def cumulCondInterferenceProjection
    (P : Job → instant → Bool) (j : Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      (cond_interference P j t).toNat

noncomputable def cumulInterferingWorkloadProjection
    (j : Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      interfering_workload j t

theorem cumulCondInterferenceProjection_guard :
    @cumul_cond_interference = @cumulCondInterferenceProjection := rfl

theorem cumulInterferingWorkloadProjection_guard :
    @cumulative_interfering_workload =
      @cumulInterferingWorkloadProjection := rfl

omit [InterferingWorkload Job] in
theorem cond_interference_eq
    (P : Job → instant → Bool) (j : Job) (t : instant) :
    cond_interference P j t = (P j t && interference j t) := rfl

omit [InterferingWorkload Job] in
theorem cumulative_interference_eq (j : Job) (t1 t2 : instant) :
    cumulative_interference j t1 t2 =
      cumul_cond_interference (fun _ _ => true) j t1 t2 := rfl

variable [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}

theorem quiet_time_eq (sched : schedule PState) (j : Job) (t : instant) :
    quiet_time sched j t =
      (decide (cumulative_interference j 0 t =
        cumulative_interfering_workload j 0 t) &&
        !pending_earlier_and_at sched j t) := rfl

end Prosa.Validation.AbstractDefinitionsInterface
