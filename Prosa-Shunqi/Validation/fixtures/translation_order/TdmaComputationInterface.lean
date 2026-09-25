import Prosa.Model.Schedule.Tdma
import Validation.fixtures.translation_order.ServiceComputationInterface

namespace Prosa.Validation.TdmaInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Validation.ServiceInterface

universe u

/-- Source-shaped computation at the TDMA readiness boundary.  Export
substitution is permitted only with the exact kernel equality below. -/
def backloggedProjection {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobCost Job] [JobArrival Job]
    [JobReady Job PState]
    (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  job_ready sched j t && !scheduledAtProjection sched j t

theorem backloggedProjection_guard :
    @backlogged = @backloggedProjection := rfl

/-- Kernel-checked Euclidean laws for the exact `Nat.mod` operation reached
through the compiled TDMA time-slot body. -/
theorem tdma_div_add_mod (x y : Nat) :
    y * (x / y) + x % y = x := Nat.div_add_mod x y

theorem tdma_mod_lt (x y : Nat) (hy : 0 < y) :
    x % y < y := Nat.mod_lt x hy

theorem tdma_mod_zero (x : Nat) : x % 0 = x := Nat.mod_zero x

#print axioms tdma_div_add_mod
#print axioms tdma_mod_lt
#print axioms tdma_mod_zero

end Prosa.Validation.TdmaInterface
