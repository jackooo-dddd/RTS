-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/fixpoint.v

import Mathlib.Tactic
import Prosa.Util.List
import Prosa.Util.Minmax
import Prosa.Util.Rel

namespace Prosa.Util.Fixpoint

/-- Fuel-bounded search for a fixed point, starting at `x` and stopping when
the next iterate exceeds `h`. Source: `find_fixpoint_from`. -/
def find_fixpoint_from (f : Nat → Nat) (x h : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      if (f x).beq x then some x
      else if (f x).ble h then find_fixpoint_from f (f x) h fuel
      else none

/-- Search from one with the horizon itself as fuel. -/
def find_fixpoint (f : Nat → Nat) (h : Nat) : Option Nat :=
  find_fixpoint_from f 1 h h

theorem ffpf_finds_fixpoint (f : Nat → Nat) (h s x fuel : Nat)
    (hfound : find_fixpoint_from f s h fuel = some x) : x = f x := by
  induction fuel generalizing s with
  | zero => simp [find_fixpoint_from] at hfound
  | succ fuel ih =>
      simp only [find_fixpoint_from] at hfound
      by_cases hEq : f s = s
      · simp [hEq] at hfound
        subst x
        exact hEq.symm
      · simp [hEq] at hfound
        exact ih (f s) hfound.2

theorem ffp_finds_fixpoint (f : Nat → Nat) (h x : Nat)
    (hfound : find_fixpoint f h = some x) : x = f x :=
  ffpf_finds_fixpoint f h 1 x h hfound

private theorem monotoneNat_le (f : Nat → Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    {a b : Nat} (hab : a ≤ b) : f a ≤ f b := by
  have h := hf a b (by simpa using hab)
  simpa using h

theorem no_fixpoint_skipped (f : Nat → Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    (_hf1 : 0 < f 1)
    (a c : Nat) (hc : c = f a) (b : Nat)
    (hab : a ≤ b) (hbc : b < c) : b ≠ f b := by
  have hmono : f a ≤ f b := monotoneNat_le f hf hab
  intro hfix
  omega

theorem ffpf_finds_least_fixpoint (f : Nat → Nat)
    (h : Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    (hf1 : 0 < f 1)
    (y s fuel : Nat)
    (hfound : find_fixpoint_from f s h fuel = some y) :
    ∀ x, s ≤ x ∧ x < y → x ≠ f x := by
  induction fuel generalizing s with
  | zero => simp [find_fixpoint_from] at hfound
  | succ fuel ih =>
      simp only [find_fixpoint_from] at hfound
      by_cases heq : f s = s
      · simp [heq] at hfound
        subst y
        intro x hx
        omega
      · by_cases hle : f s ≤ h
        · simp [heq, hle] at hfound
          intro x ⟨hsx, hxy⟩
          by_cases hfx : f s ≤ x
          · exact ih (f s) hfound x ⟨hfx, hxy⟩
          · exact no_fixpoint_skipped f hf hf1 s (f s) rfl x hsx (by omega)
        · simp [heq, hle] at hfound

theorem ffp_finds_least_fixpoint (f : Nat → Nat)
    (h : Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    (hf1 : 0 < f 1)
    (x y : Nat) (hxy : 0 < x ∧ x < y)
    (hfound : find_fixpoint f h = some y) : x ≠ f x :=
  ffpf_finds_least_fixpoint f h hf hf1 y 1 h hfound x
    ⟨by omega, hxy.2⟩

theorem ffpf_finds_positive_fixpoint (f : Nat → Nat)
    (h : Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    (hf1 : 0 < f 1) (s fuel x : Nat)
    (hfound : some x = find_fixpoint_from f s h fuel)
    (hs : 0 < s) : 0 < x := by
  induction fuel generalizing s with
  | zero => simp [find_fixpoint_from] at hfound
  | succ fuel ih =>
      simp only [find_fixpoint_from] at hfound
      by_cases heq : f s = s
      · simp [heq] at hfound
        simpa [hfound] using hs
      · by_cases hle : f s ≤ h
        · simp [heq, hle] at hfound
          have hpos : 0 < f s := by
            have hmono : f 1 ≤ f s := monotoneNat_le f hf (by omega)
            omega
          exact ih (f s) hfound hpos
        · simp [heq, hle] at hfound

theorem ffp_finds_positive_fixpoint (f : Nat → Nat)
    (h : Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    (hf1 : 0 < f 1) (x : Nat)
    (hfound : some x = find_fixpoint f h) : 0 < x :=
  ffpf_finds_positive_fixpoint f h hf hf1 1 h x hfound (by omega)

theorem ffpf_finds_none (f : Nat → Nat)
    (h : Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    (hf1 : 0 < f 1) (s fuel : Nat)
    (hsf : s ≤ f s) (hfuel : h - s ≤ fuel)
    (hfound : find_fixpoint_from f s h fuel = none) :
    ∀ x, s ≤ x ∧ x < h → x ≠ f x := by
  induction fuel generalizing s with
  | zero =>
      intro x ⟨hsx, hxh⟩
      omega
  | succ fuel ih =>
      simp only [find_fixpoint_from] at hfound
      by_cases heq : f s = s
      · simp [heq] at hfound
      · by_cases hle : f s ≤ h
        · simp [heq, hle] at hfound
          intro x ⟨hsx, hxh⟩
          by_cases hfx : f s ≤ x
          · have hff : f s ≤ f (f s) := monotoneNat_le f hf hsf
            have hnext : h - f s ≤ fuel := by omega
            exact ih (f s) hff hnext hfound x ⟨hfx, hxh⟩
          · exact no_fixpoint_skipped f hf hf1 s (f s) rfl x hsx (by omega)
        · intro x ⟨hsx, hxh⟩
          exact no_fixpoint_skipped f hf hf1 s (f s) rfl x hsx (by omega)

theorem ffp_finds_none (f : Nat → Nat)
    (h : Nat)
    (hf : Rel.monotone (fun a b : Nat => decide (a ≤ b)) f)
    (hf1 : 0 < f 1)
    (hfound : find_fixpoint f h = none) :
    ∀ x, 0 < x ∧ x < h → x ≠ f x := by
  intro x ⟨hx, hxh⟩
  exact ffpf_finds_none f h hf hf1 1 h (by omega) (by omega)
    hfound x ⟨by omega, hxh⟩

/-- Conditional maximum of the per-element fixed points, provided each
search-space element has one. Source: `find_max_fixpoint_of_seq`. -/
def find_max_fixpoint_of_seq (f : Nat → Nat → Nat)
    (sp : List Nat) (h : Nat) : Option Nat :=
  let fixpoints := sp.map (fun s => find_fixpoint (f s) h)
  let max := Minmax.bigMaxListCond fixpoints Option.isSome
    (fun fp => fp.getD 0)
  if fixpoints.all Option.isSome then some max else none

/-- Predicate-defined search space `[0,L)`, preserving source order. -/
def find_max_fixpoint (L : Nat) (P : Nat → Bool)
    (f : Nat → Nat → Nat) (h : Nat) : Option Nat :=
  let sp := (_root_.List.range L).filter (fun s => P s)
  if (_root_.List.range L).any P then find_max_fixpoint_of_seq f sp h else none

theorem fmfs_finds_fixpoint (f : Nat → Nat → Nat)
    (sp : List Nat) (h x : Nat) (hne : sp ≠ [])
    (hfound : find_max_fixpoint_of_seq f sp h = some x) :
    ∃ a, a ∈ sp ∧ x = f a x := by
  let fps := sp.map (fun s => find_fixpoint (f s) h)
  have hall : fps.all Option.isSome = true := by
    cases hAll : fps.all Option.isSome with
    | true => rfl
    | false => simp [find_max_fixpoint_of_seq, fps, hAll] at hfound
  have hnonempty : fps.isEmpty = false := by
    cases sp with
    | nil => exact False.elim (hne rfl)
    | cons a tail => rfl
  have hany := Prosa.Util.List.has_all_nilp fps Option.isSome hall hnonempty
  obtain ⟨w, hw, hsome, hmax⟩ :=
    Minmax.bigmax_witness (xs := fps) (P := Option.isSome)
      (fun fp => fp.getD 0) hany
  obtain ⟨a, ha, haw⟩ := _root_.List.mem_map.mp hw
  cases w with
  | none => simp at hsome
  | some v =>
      have hv : v = x := by
        simp [find_max_fixpoint_of_seq, fps, hall] at hfound
        simpa using hmax.trans hfound
      have hfix : find_fixpoint (f a) h = some v := by
        simpa using haw
      subst v
      exact ⟨a, ha, (ffp_finds_fixpoint (f a) h x hfix)⟩

theorem fmfs_is_maximum (f : Nat → Nat → Nat)
    (sp : List Nat) (h s r : Nat)
    (hfound : some r = find_max_fixpoint_of_seq f sp h)
    (hs : s ∈ sp) :
    ∃ v, some v = find_fixpoint (f s) h ∧ v ≤ r := by
  let fps := sp.map (fun a => find_fixpoint (f a) h)
  have hall : fps.all Option.isSome = true := by
    cases hAll : fps.all Option.isSome with
    | true => rfl
    | false => simp [find_max_fixpoint_of_seq, fps, hAll] at hfound
  have hmem : find_fixpoint (f s) h ∈ fps :=
    _root_.List.mem_map.mpr ⟨s, hs, rfl⟩
  have hsome : (find_fixpoint (f s) h).isSome = true :=
    (_root_.List.all_eq_true.mp hall) _ hmem
  cases hfp : find_fixpoint (f s) h with
  | none => simp [hfp] at hsome
  | some v =>
      have hbound := Minmax.leq_bigmax_cond_seq
        (fun fp : Option Nat => fp.getD 0) Option.isSome fps
        (some v) (by simpa [hfp] using hmem) (by rfl)
      have hr : Minmax.bigMaxListCond fps Option.isSome
          (fun fp => fp.getD 0) = r := by
        simpa [find_max_fixpoint_of_seq, fps, hall] using hfound.symm
      exact ⟨v, rfl, by simpa [hr] using hbound⟩

theorem fmf_finds_fixpoint (L : Nat) (P : Nat → Bool)
    (f : Nat → Nat → Nat) (h x : Nat)
    (hfound : find_max_fixpoint L P f h = some x) :
    ∃ a, (a < L ∧ P a = true) ∧ x = f a x := by
  have hany : (_root_.List.range L).any P = true := by
    cases hAny : (_root_.List.range L).any P with
    | true => rfl
    | false => simp [find_max_fixpoint, hAny] at hfound
  obtain ⟨a₀, ha₀, hPa₀⟩ := _root_.List.any_eq_true.mp hany
  have hsp : ((_root_.List.range L).filter P) ≠ [] := by
    intro hempty
    have hmem : a₀ ∈ (_root_.List.range L).filter P :=
      _root_.List.mem_filter.mpr ⟨ha₀, hPa₀⟩
    simp [hempty] at hmem
  have hseq : find_max_fixpoint_of_seq f
      ((_root_.List.range L).filter P) h = some x := by
    simpa [find_max_fixpoint, hany] using hfound
  obtain ⟨a, ha, hfix⟩ :=
    fmfs_finds_fixpoint f ((_root_.List.range L).filter P) h x hsp hseq
  obtain ⟨harange, hPa⟩ := _root_.List.mem_filter.mp ha
  exact ⟨a, ⟨_root_.List.mem_range.mp harange, hPa⟩, hfix⟩

theorem fmf_is_maximum (L : Nat) (P : Nat → Bool)
    (f : Nat → Nat → Nat) (h s r : Nat)
    (hfound : some r = find_max_fixpoint L P f h)
    (hs : s < L ∧ P s = true) :
    ∃ v, some v = find_fixpoint (f s) h ∧ v ≤ r := by
  have hsrange : s ∈ _root_.List.range L :=
    _root_.List.mem_range.mpr hs.1
  have hsp : s ∈ (_root_.List.range L).filter P :=
    _root_.List.mem_filter.mpr ⟨hsrange, hs.2⟩
  have hany : (_root_.List.range L).any P = true :=
    _root_.List.any_eq_true.mpr ⟨s, hsrange, hs.2⟩
  have hseq : some r = find_max_fixpoint_of_seq f
      ((_root_.List.range L).filter P) h := by
    simpa [find_max_fixpoint, hany] using hfound
  exact fmfs_is_maximum f ((_root_.List.range L).filter P)
    h s r hseq hsp

end Prosa.Util.Fixpoint
