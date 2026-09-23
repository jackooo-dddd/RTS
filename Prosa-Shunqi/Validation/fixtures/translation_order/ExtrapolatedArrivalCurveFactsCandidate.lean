-- Rank 36 proof-development fixture. Not production and not coverage.
import Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

namespace Prosa.Implementation.Facts.ExtrapolatedArrivalCurve

open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

theorem ltn_steps_is_transitive (a b c : Nat × Nat)
    (hab : ltn_steps a b = true) (hbc : ltn_steps b c = true) :
    ltn_steps a c = true := by
  simp only [ltn_steps, Bool.and_eq_true, decide_eq_true_eq] at *
  exact ⟨lt_trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩

theorem leq_steps_is_reflexive (a : Nat × Nat) :
    leq_steps a a = true := by
  simp [leq_steps]

theorem leq_steps_is_transitive (a b c : Nat × Nat)
    (hab : leq_steps a b = true) (hbc : leq_steps b c = true) :
    leq_steps a c = true := by
  simp only [leq_steps, Bool.and_eq_true, decide_eq_true_eq] at *
  exact ⟨le_trans hab.1 hbc.1, le_trans hab.2 hbc.2⟩

private theorem ltn_steps_implies_leq_steps (a b : Nat × Nat)
    (hab : ltn_steps a b = true) : leq_steps a b = true := by
  simp only [ltn_steps, leq_steps, Bool.and_eq_true, decide_eq_true_eq] at *
  exact ⟨le_of_lt hab.1, le_of_lt hab.2⟩

private theorem sortedFrom_ltn_implies_leq (a : Nat × Nat)
    (xs : List (Nat × Nat))
    (h : sortedBoolFrom ltn_steps a xs = true) :
    sortedBoolFrom leq_steps a xs = true := by
  induction xs generalizing a with
  | nil => simp [sortedBoolFrom]
  | cons b rest ih =>
      simp only [sortedBoolFrom, Bool.and_eq_true] at h ⊢
      exact ⟨ltn_steps_implies_leq_steps a b h.1, ih b h.2⟩

theorem sorted_ltn_steps_imply_sorted_leq_steps_steps
    (ac_prefix : ArrivalCurvePrefix)
    (hsorted : sorted_ltn_steps ac_prefix = true)
    (_hnoinf : no_inf_arrivals ac_prefix = true) :
    sorted_leq_steps ac_prefix = true := by
  unfold sorted_ltn_steps at hsorted
  unfold sorted_leq_steps
  cases hsteps : steps_of ac_prefix with
  | nil => simp [sortedBool, hsteps]
  | cons a rest =>
      simp only [sortedBool, hsteps] at hsorted ⊢
      exact sortedFrom_ltn_implies_leq a rest hsorted

private theorem filter_zero_nil_of_sortedFrom (a : Nat × Nat)
    (xs : List (Nat × Nat))
    (hsorted : sortedBoolFrom ltn_steps a xs = true) :
    xs.filter (fun p => decide (p.1 ≤ 0)) = [] := by
  induction xs generalizing a with
  | nil => rfl
  | cons b rest ih =>
      simp only [sortedBoolFrom, Bool.and_eq_true] at hsorted
      have hlt : a.1 < b.1 := by
        have hpair : a.1 < b.1 ∧ a.2 < b.2 := by
          simpa [ltn_steps, Bool.and_eq_true, decide_eq_true_eq] using hsorted.1
        exact hpair.1
      have hb : ¬ b.1 ≤ 0 := by omega
      have hbf : decide (b.1 ≤ 0) = false := by simp [hb]
      simp only [List.filter_cons, hbf, Bool.false_eq_true, ↓reduceIte]
      exact ih b hsorted.2

theorem step_at_0_is_00 (ac_prefix : ArrivalCurvePrefix)
    (hsorted : sorted_ltn_steps ac_prefix = true)
    (hnoinf : no_inf_arrivals ac_prefix = true) :
    step_at ac_prefix 0 = (0, 0) := by
  rcases ac_prefix with ⟨h, xs⟩
  cases xs with
  | nil => simp [step_at, steps_of]
  | cons p rest =>
      have hsorted' : sortedBoolFrom ltn_steps p rest = true := by
        simpa [sorted_ltn_steps, sortedBool, steps_of] using hsorted
      have hrest := filter_zero_nil_of_sortedFrom p rest hsorted'
      rcases Nat.eq_zero_or_pos p.1 with hp0 | hp0
      · have hfilter :
            (p :: rest).filter (fun step => decide (step.1 ≤ 0)) = [p] := by
          simp only [List.filter_cons, hrest]
          simp [hp0]
        have hstep : step_at (h, p :: rest) 0 = p := by
          simp only [step_at, steps_of, hfilter]
          rfl
        have hvalue : p.2 = 0 := by
          have hzero := of_decide_eq_true hnoinf
          simpa [no_inf_arrivals, value_at, hstep] using hzero
        have hp : p = (0, 0) := by
          cases p with
          | mk t v => simp only at hp0 hvalue; simp [hp0, hvalue]
        exact hstep.trans hp
      · have hp : ¬ p.1 ≤ 0 := Nat.not_le.mpr hp0
        have hfilter :
            (p :: rest).filter (fun step => decide (step.1 ≤ 0)) = [] := by
          simp only [List.filter_cons, hrest]
          simp [hp]
        simp only [step_at, steps_of, hfilter]
        rfl

private theorem getLastD_filter_snd_eq_foldl
    (xs : List (Nat × Nat)) (p : Nat × Nat → Bool)
    (fallback : Nat × Nat) :
    ((xs.filter p).getLastD fallback).2 =
      xs.foldl (fun value step => if p step then step.2 else value) fallback.2 := by
  induction xs generalizing fallback with
  | nil => rfl
  | cons x rest ih =>
      by_cases hx : p x = true
      · simp only [List.filter_cons, List.foldl_cons, hx, ↓reduceIte]
        rw [List.getLastD_cons]
        exact ih x
      · have hfalse : p x = false := Bool.eq_false_iff.mpr hx
        simp only [List.filter_cons, List.foldl_cons, hfalse,
          Bool.false_eq_true, ↓reduceIte]
        exact ih fallback

private theorem valueFold_mono (prev : Nat × Nat)
    (xs : List (Nat × Nat)) (t1 t2 acc1 acc2 : Nat)
    (hsorted : sortedBoolFrom leq_steps prev xs = true)
    (ht : t1 ≤ t2) (hacc : acc1 ≤ acc2) (hbound : acc2 ≤ prev.2) :
    xs.foldl (fun value step => if decide (step.1 ≤ t1) then step.2 else value) acc1 ≤
    xs.foldl (fun value step => if decide (step.1 ≤ t2) then step.2 else value) acc2 := by
  induction xs generalizing prev acc1 acc2 with
  | nil => exact hacc
  | cons x rest ih =>
      simp only [sortedBoolFrom, Bool.and_eq_true] at hsorted
      have hval : prev.2 ≤ x.2 := by
        have hpair : prev.1 ≤ x.1 ∧ prev.2 ≤ x.2 := by
          simpa [leq_steps, Bool.and_eq_true, decide_eq_true_eq]
            using hsorted.1
        exact hpair.2
      simp only [List.foldl_cons]
      by_cases h1 : x.1 ≤ t1
      · have h2 : x.1 ≤ t2 := le_trans h1 ht
        simpa [h1, h2] using
          (ih x x.2 x.2 hsorted.2 (Nat.le_refl _) (Nat.le_refl _))
      · by_cases h2 : x.1 ≤ t2
        · have hnew : acc1 ≤ x.2 := le_trans hacc (le_trans hbound hval)
          simpa [h1, h2] using
            (ih x acc1 x.2 hsorted.2 hnew (Nat.le_refl _))
        · simpa [h1, h2] using
            (ih x acc1 acc2 hsorted.2 hacc (le_trans hbound hval))

theorem value_at_monotone (ac_prefix : ArrivalCurvePrefix)
    (hsorted : sorted_leq_steps ac_prefix = true)
    (t1 t2 : Nat) (ht : t1 ≤ t2) :
    value_at ac_prefix t1 ≤ value_at ac_prefix t2 := by
  rcases ac_prefix with ⟨h, xs⟩
  have hsorted0 : sortedBoolFrom leq_steps (0, 0) xs = true := by
    cases xs with
    | nil => rfl
    | cons x rest =>
        have htail : sortedBoolFrom leq_steps x rest = true := by
          simpa [sorted_leq_steps, sortedBool, steps_of] using hsorted
        simp only [sortedBoolFrom, Bool.and_eq_true]
        exact ⟨by simp [leq_steps], htail⟩
  have hfold := valueFold_mono (0, 0) xs t1 t2 0 0 hsorted0 ht
    (Nat.le_refl _) (Nat.le_refl _)
  simpa only [value_at, step_at, steps_of,
    getLastD_filter_snd_eq_foldl] using hfold

private theorem filter_le_nil_of_sortedFrom (prev : Nat × Nat)
    (xs : List (Nat × Nat)) (cutoff : Nat)
    (hsorted : sortedBoolFrom ltn_steps prev xs = true)
    (hcut : cutoff ≤ prev.1) :
    xs.filter (fun p => decide (p.1 ≤ cutoff)) = [] := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x rest ih =>
      simp only [sortedBoolFrom, Bool.and_eq_true] at hsorted
      have hlt : prev.1 < x.1 := by
        have hp : prev.1 < x.1 ∧ prev.2 < x.2 := by
          simpa [ltn_steps, Bool.and_eq_true, decide_eq_true_eq] using hsorted.1
        exact hp.1
      have hx : ¬ x.1 ≤ cutoff := by omega
      have hxf : decide (x.1 ≤ cutoff) = false := by simp [hx]
      simp only [List.filter_cons, hxf, Bool.false_eq_true, ↓reduceIte]
      exact ih x hsorted.2 (le_trans hcut (le_of_lt hlt))

private theorem last_selected_of_sortedFrom (prev : Nat × Nat)
    (xs : List (Nat × Nat))
    (hsorted : sortedBoolFrom ltn_steps prev xs = true) :
    ∀ p, p ∈ xs → ∀ fallback,
      ((xs.filter (fun q => decide (q.1 ≤ p.1))).getLastD fallback) = p := by
  induction xs generalizing prev with
  | nil => intro p hmem; cases hmem
  | cons x rest ih =>
      simp only [sortedBoolFrom, Bool.and_eq_true] at hsorted
      intro p hmem fallback
      rcases List.mem_cons.mp hmem with rfl | hrest
      · have htail := filter_le_nil_of_sortedFrom p rest p.1 hsorted.2
          (Nat.le_refl _)
        have hxx : decide (p.1 ≤ p.1) = true := by simp
        simp only [List.filter_cons, hxx, ↓reduceIte, htail]
        rfl
      · by_cases hx : x.1 ≤ p.1
        · have hxf : decide (x.1 ≤ p.1) = true := by simp [hx]
          simp only [List.filter_cons, hxf, ↓reduceIte]
          rw [List.getLastD_cons]
          exact ih x hsorted.2 p hrest x
        · have hxf : decide (x.1 ≤ p.1) = false := by simp [hx]
          simp only [List.filter_cons, hxf, Bool.false_eq_true, ↓reduceIte]
          exact ih x hsorted.2 p hrest fallback

private theorem last_selected_of_sorted (xs : List (Nat × Nat))
    (hsorted : sortedBool ltn_steps xs = true) :
    ∀ p, p ∈ xs → ∀ fallback,
      ((xs.filter (fun q => decide (q.1 ≤ p.1))).getLastD fallback) = p := by
  cases xs with
  | nil => intro p hmem; cases hmem
  | cons x rest =>
      have htail : sortedBoolFrom ltn_steps x rest = true := by
        simpa [sortedBool] using hsorted
      intro p hmem fallback
      rcases List.mem_cons.mp hmem with rfl | hrest
      · have hnil := filter_le_nil_of_sortedFrom p rest p.1 htail
          (Nat.le_refl _)
        have hxx : decide (p.1 ≤ p.1) = true := by simp
        simp only [List.filter_cons, hxx, ↓reduceIte, hnil]
        rfl
      · by_cases hx : x.1 ≤ p.1
        · have hxf : decide (x.1 ≤ p.1) = true := by simp [hx]
          simp only [List.filter_cons, hxf, ↓reduceIte]
          rw [List.getLastD_cons]
          exact last_selected_of_sortedFrom x rest htail p hrest x
        · have hxf : decide (x.1 ≤ p.1) = false := by simp [hx]
          simp only [List.filter_cons, hxf, Bool.false_eq_true, ↓reduceIte]
          exact last_selected_of_sortedFrom x rest htail p hrest fallback

theorem step_at_agrees_with_steps_of (ac_prefix : ArrivalCurvePrefix)
    (hsorted : sorted_ltn_steps ac_prefix = true)
    (t v : Nat) (hmem : (t, v) ∈ steps_of ac_prefix) :
    step_at ac_prefix t = (t, v) := by
  have hsorted' : sortedBool ltn_steps (steps_of ac_prefix) = true := hsorted
  simpa [step_at] using
    last_selected_of_sorted (steps_of ac_prefix) hsorted' (t, v) hmem (0, 0)

private theorem filter_next_eq_of_no_step (xs : List (Nat × Nat)) (t : Nat)
    (hno : ∀ x ∈ xs, x.1 ≠ t + 1) :
    xs.filter (fun x => decide (x.1 ≤ t + 1)) =
      xs.filter (fun x => decide (x.1 ≤ t)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx : x.1 ≠ t + 1 := hno x (by simp)
      have hrest : ∀ y ∈ rest, y.1 ≠ t + 1 := by
        intro y hy
        exact hno y (by simp [hy])
      have hiff : x.1 ≤ t + 1 ↔ x.1 ≤ t := by omega
      have hdec : decide (x.1 ≤ t + 1) = decide (x.1 ≤ t) := by
        by_cases h : x.1 ≤ t
        · have h' : x.1 ≤ t + 1 := hiff.mpr h
          simp [h, h']
        · have h' : ¬ x.1 ≤ t + 1 := fun q => h (hiff.mp q)
          simp [h, h']
      simp only [List.filter_cons, hdec, ih hrest]

theorem value_at_change_is_in_steps_of (ac_prefix : ArrivalCurvePrefix)
    (_hsorted : sorted_leq_steps ac_prefix = true)
    (_hnoinf : no_inf_arrivals ac_prefix = true)
    (t : Nat) (hchange : value_at ac_prefix t < value_at ac_prefix (t + 1)) :
    ∃ v, (t + 1, v) ∈ steps_of ac_prefix := by
  by_contra hnone
  have hno : ∀ x ∈ steps_of ac_prefix, x.1 ≠ t + 1 := by
    intro x hx heq
    apply hnone
    refine ⟨x.2, ?_⟩
    have hpair : x = (t + 1, x.2) := by
      cases x with
      | mk s v => simp only at heq; simp [heq]
    rw [← hpair]
    exact hx
  have hfilter := filter_next_eq_of_no_step (steps_of ac_prefix) t hno
  have hvalue : value_at ac_prefix (t + 1) = value_at ac_prefix t := by
    simp only [value_at, step_at]
    rw [hfilter]
  omega

theorem extrapolated_arrival_curve_is_monotone
    (ac_prefix : ArrivalCurvePrefix)
    (hpositive : positive_horizon ac_prefix = true)
    (hsorted : sorted_leq_steps ac_prefix = true)
    (t1 t2 : Nat) (ht : t1 ≤ t2) :
    extrapolated_arrival_curve ac_prefix t1 ≤
      extrapolated_arrival_curve ac_prefix t2 := by
  let h := horizon_of ac_prefix
  have hh : 0 < h := by
    have hp := of_decide_eq_true hpositive
    simpa [positive_horizon, h] using hp
  have hq : t1 / h ≤ t2 / h := Nat.div_le_div_right ht
  have hv (a b : Nat) (hab : a ≤ b) :
      value_at ac_prefix a ≤ value_at ac_prefix b :=
    value_at_monotone ac_prefix hsorted a b hab
  change t1 / h * value_at ac_prefix h + value_at ac_prefix (t1 % h) ≤
    t2 / h * value_at ac_prefix h + value_at ac_prefix (t2 % h)
  by_cases hsame : t1 / h = t2 / h
  · have hr : t1 % h ≤ t2 % h := by
      have hfirst := Nat.mod_add_div t1 h
      have hsecond := Nat.mod_add_div t2 h
      rw [← hsame] at hsecond
      omega
    rw [hsame]
    exact Nat.add_le_add_left (hv _ _ hr) _
  · have hstrict : t1 / h < t2 / h := Nat.lt_of_le_of_ne hq hsame
    have hbound : value_at ac_prefix (t1 % h) ≤ value_at ac_prefix h :=
      hv _ _ (Nat.le_of_lt (Nat.mod_lt _ hh))
    have hsucc : t1 / h + 1 ≤ t2 / h := by omega
    calc
      t1 / h * value_at ac_prefix h + value_at ac_prefix (t1 % h)
          ≤ t1 / h * value_at ac_prefix h + value_at ac_prefix h :=
            Nat.add_le_add_left hbound _
      _ = (t1 / h + 1) * value_at ac_prefix h := by ring
      _ ≤ t2 / h * value_at ac_prefix h := Nat.mul_le_mul_right _ hsucc
      _ ≤ t2 / h * value_at ac_prefix h + value_at ac_prefix (t2 % h) :=
        Nat.le_add_right _ _

theorem extrapolated_arrival_curve_change
    (ac_prefix : ArrivalCurvePrefix)
    (hpositive : positive_horizon ac_prefix = true)
    (hsorted : sorted_leq_steps ac_prefix = true)
    (t : Nat)
    (hchange : extrapolated_arrival_curve ac_prefix t ≠
      extrapolated_arrival_curve ac_prefix (t + 1)) :
    t / horizon_of ac_prefix < (t + 1) / horizon_of ac_prefix ∨
      (t / horizon_of ac_prefix = (t + 1) / horizon_of ac_prefix ∧
        value_at ac_prefix (t % horizon_of ac_prefix) <
          value_at ac_prefix ((t + 1) % horizon_of ac_prefix)) := by
  let h := horizon_of ac_prefix
  have ht : t ≤ t + 1 := Nat.le_succ t
  have hmon := extrapolated_arrival_curve_is_monotone
    ac_prefix hpositive hsorted t (t + 1) ht
  have hstrict : extrapolated_arrival_curve ac_prefix t <
      extrapolated_arrival_curve ac_prefix (t + 1) :=
    Nat.lt_of_le_of_ne hmon hchange
  have hquot : t / h ≤ (t + 1) / h := Nat.div_le_div_right ht
  rcases Nat.lt_or_eq_of_le hquot with hlt | heq
  · exact Or.inl hlt
  · right
    refine ⟨heq, ?_⟩
    change t / h * value_at ac_prefix h + value_at ac_prefix (t % h) <
      (t + 1) / h * value_at ac_prefix h +
        value_at ac_prefix ((t + 1) % h) at hstrict
    rw [← heq] at hstrict
    change value_at ac_prefix (t % h) <
      value_at ac_prefix ((t + 1) % h)
    omega

#print axioms ltn_steps_is_transitive
#print axioms leq_steps_is_reflexive
#print axioms leq_steps_is_transitive
#print axioms sorted_ltn_steps_imply_sorted_leq_steps_steps
#print axioms step_at_0_is_00
#print axioms value_at_monotone
#print axioms step_at_agrees_with_steps_of
#print axioms value_at_change_is_in_steps_of
#print axioms extrapolated_arrival_curve_is_monotone
#print axioms extrapolated_arrival_curve_change

end Prosa.Implementation.Facts.ExtrapolatedArrivalCurve
