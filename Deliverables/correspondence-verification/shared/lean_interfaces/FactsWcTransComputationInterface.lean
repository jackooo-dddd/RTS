import Prosa.Analysis.Transform.WcTrans
import Validation.fixtures.translation_order.TransformPrefixComputationInterface

/-!
Export root for `analysis/transform/wc_trans.v`: the six definitions together
with the accepted transform-prefix export root (preemption-parameter closure,
with its Nat-list `max0` equations), and kernel-checked equations, at the ideal
processor, for the structurally recursive `search_arg` and `prefix_map` and for
`replace_at` (hence `swapped`).  Every equation is proved in Lean and exported
with its proof.
-/

namespace Prosa.Validation.WcTransInterface

open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.Swap
open Prosa.Util.SearchArg

variable {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job]

theorem production_search_arg_zero (f : Nat → Option Job) (P : Option Job → Bool)
    (R : Option Job → Option Job → Bool) (a : Nat) :
    search_arg f P R a 0 = none := by
  simp [search_arg]

theorem production_search_arg_succ_ge (f : Nat → Option Job) (P : Option Job → Bool)
    (R : Option Job → Option Job → Bool) (a b : Nat) (h : ¬ a < b + 1) :
    search_arg f P R a (b + 1) = none := by
  rw [search_arg, if_neg h]

theorem production_search_arg_succ_none_true (f : Nat → Option Job) (P : Option Job → Bool)
    (R : Option Job → Option Job → Bool) (a b : Nat)
    (h : a < b + 1) (hn : search_arg f P R a b = none) (hp : P (f b) = true) :
    search_arg f P R a (b + 1) = some b := by
  rw [search_arg, if_pos h]; simp only [hn, hp, if_true]

theorem production_search_arg_succ_none_false (f : Nat → Option Job) (P : Option Job → Bool)
    (R : Option Job → Option Job → Bool) (a b : Nat)
    (h : a < b + 1) (hn : search_arg f P R a b = none) (hp : P (f b) = false) :
    search_arg f P R a (b + 1) = none := by
  rw [search_arg, if_pos h]; simp only [hn, hp]; rfl

theorem production_search_arg_succ_some_true (f : Nat → Option Job) (P : Option Job → Bool)
    (R : Option Job → Option Job → Bool) (a b x : Nat)
    (h : a < b + 1) (hs : search_arg f P R a b = some x) (hp : (P (f b) && R (f b) (f x)) = true) :
    search_arg f P R a (b + 1) = some b := by
  rw [search_arg, if_pos h]; simp only [hs, hp, if_true]

theorem production_search_arg_succ_some_false (f : Nat → Option Job) (P : Option Job → Bool)
    (R : Option Job → Option Job → Bool) (a b x : Nat)
    (h : a < b + 1) (hs : search_arg f P R a b = some x) (hp : (P (f b) && R (f b) (f x)) = false) :
    search_arg f P R a (b + 1) = some x := by
  rw [search_arg, if_pos h]; simp only [hs, hp]; rfl

theorem production_prefix_map_zero (sched : schedule (processor_state Job))
    (f : schedule (processor_state Job) → instant → schedule (processor_state Job)) :
    prefix_map sched f 0 = sched := rfl

theorem production_prefix_map_succ (sched : schedule (processor_state Job))
    (f : schedule (processor_state Job) → instant → schedule (processor_state Job)) (t : Nat) :
    prefix_map sched f (t + 1) = f (prefix_map sched f t) t := rfl

theorem production_replace_at_same (sched : schedule (processor_state Job)) (t' : instant)
    (ns : (processor_state Job).State) (t : instant) (h : t = t') :
    replace_at sched t' ns t = ns := by
  subst h; simp [replace_at]

theorem production_replace_at_other (sched : schedule (processor_state Job)) (t' : instant)
    (ns : (processor_state Job).State) (t : instant) (h : ¬ t = t') :
    replace_at sched t' ns t = sched t := by
  simp only [replace_at]
  rw [if_neg]
  intro e
  exact h (beq_iff_eq.mp e).symm

end Prosa.Validation.WcTransInterface
