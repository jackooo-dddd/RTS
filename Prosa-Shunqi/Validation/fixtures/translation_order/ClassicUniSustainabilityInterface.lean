import Prosa.Classic.Model.Schedule.Uni.Sustainability

/-!
Validation-only interface for `classic/model/schedule/uni/sustainability.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicUniSustainabilityInterface

open Prosa.Classic.Model.Schedule.Uni.Sustainability.Sustainability

universe u

/-- `find_param` on the empty list and on a cons cell (kernel-checked; used by the Rocq certificate as
propositional equations only). -/
theorem xsu_find_param_nil {Job : Type u} [DecidableEq Job] (l : parameter_label) :
    find_param (Job := Job) l [] = job_parameter.param l (default_val l) := rfl

theorem xsu_find_param_cons {Job : Type u} [DecidableEq Job] (l : parameter_label) (p0 : job_parameter Job)
    (s : List (job_parameter Job)) :
    find_param l (p0 :: s) = if p0.p_label = l then p0 else find_param l s := by
  unfold find_param
  rw [List.findIdx_cons]
  by_cases h : p0.p_label = l
  · rw [if_pos h]
    have hd : decide (p0.p_label = l) = true := decide_eq_true h
    show List.getD (p0 :: s) (cond (decide (p0.p_label = l)) 0 _) _ = p0
    rw [hd]; rfl
  · rw [if_neg h]
    have hd : decide (p0.p_label = l) = false := decide_eq_false h
    show List.getD (p0 :: s) (cond (decide (p0.p_label = l)) 0 _) _ = _
    rw [hd]; rfl

/-- `get_param_function` on a parameter with the requested label, resp. with another label. -/
theorem xsu_get_param_same {Job : Type u} [DecidableEq Job] (l : parameter_label) (f : type_of_label (Job := Job) l) :
    get_param_function l (job_parameter.param l f) = f := by
  cases l <;> rfl

theorem xsu_get_param_other {Job : Type u} [DecidableEq Job] (l l' : parameter_label) (f : type_of_label (Job := Job) l')
    (h : l' ≠ l) : get_param_function l (job_parameter.param l' f) = default_val l := by
  cases l <;> cases l' <;> first | rfl | exact absurd rfl h

end Prosa.Validation.ClassicUniSustainabilityInterface
