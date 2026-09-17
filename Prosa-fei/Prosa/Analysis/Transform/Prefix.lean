-- Translated from: ../rt-proofs/analysis/transform/prefix.v
import Prosa.Analysis.Facts.Behavior.All

namespace Prosa.Analysis.Transform.Prefix

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule

section SchedulePrefixMap

variable {Job : JobType}
variable {PState : Type _}
variable [ProcessorState Job PState]

def prefix_map
    (sched : schedule PState)
    (f : schedule PState → instant → schedule PState)
    (horizon : instant) : schedule PState :=
  match horizon with
  | 0 => sched
  | Nat.succ t =>
    let pfx := prefix_map sched f t
    f pfx t

section PropertyPreservation

variable (P : schedule PState → Prop)
variable (f : schedule PState → instant → schedule PState)
variable (H_f_maintains_P : ∀ sched t, P sched → P (f sched t))

include H_f_maintains_P in
theorem prefix_map_property_invariance :
    ∀ sched h, P sched → P (prefix_map sched f h) := by
  intro sched h P_sched
  induction h with
  | zero => exact P_sched
  | succ n ih => exact H_f_maintains_P _ _ ih

end PropertyPreservation

section PointwiseProperty

variable (P : schedule PState → Prop)
variable (Q : schedule PState → instant → Prop)
variable (f : schedule PState → instant → schedule PState)

variable (H_f_maintains_P :
    ∀ sched t_ref, P sched → P (f sched t_ref))

variable (H_f_grows_Q :
    ∀ sched t_ref,
      P sched →
      (∀ t', t' < t_ref → Q sched t') →
      ∀ t', t' ≤ t_ref → Q (f sched t_ref) t')

include H_f_maintains_P H_f_grows_Q in
theorem prefix_map_pointwise_property :
    ∀ sched horizon,
      P sched →
      ∀ t,
        t < horizon →
        Q (prefix_map sched f horizon) t := by
  intro sched horizon P_holds
  induction horizon with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero t)
  | succ h ih =>
    intro t ht
    show Q (f (prefix_map sched f h) h) t
    apply H_f_grows_Q
    · exact prefix_map_property_invariance P f H_f_maintains_P sched h P_holds
    · exact ih
    · exact Nat.lt_succ_iff.mp ht

end PointwiseProperty

end SchedulePrefixMap

end Prosa.Analysis.Transform.Prefix
