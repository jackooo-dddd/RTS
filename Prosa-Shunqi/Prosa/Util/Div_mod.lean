-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/div_mod.v

import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Div
import Prosa.Util.Nat
import Prosa.Util.Subadditivity

namespace Prosa.Util.Div_mod

open Prosa.Util.Subadditivity

theorem eqdivn_leqmodn (t₁ t₂ h : Nat) (hle : t₁ ≤ t₂)
    (hdiv : t₁ / h = t₂ / h) : t₁ % h ≤ t₂ % h := by
  have ht₁ := Nat.div_add_mod t₁ h
  have ht₂ := Nat.div_add_mod t₂ h
  rw [hdiv] at ht₁
  omega

theorem ltdivn_dvdn (x y : Nat) (hlt : x / y < (x + 1) / y) :
    y ∣ x + 1 := by
  by_cases hy0 : y = 0
  · subst y
    simp at hlt
  · have hy : 0 < y := Nat.pos_of_ne_zero hy0
    have hmul : (x / y + 1) * y ≤ x + 1 :=
      (Nat.le_div_iff_mul_le hy).mp (Nat.succ_le_iff.mpr hlt)
    have hdecomp : x = (x / y) * y + x % y := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod x y).symm
    have hrem : x % y < y := Nat.mod_lt x hy
    have hmul' : (x / y) * y + y ≤ x + 1 := by
      simpa [Nat.add_mul] using hmul
    have heq : x + 1 = (x / y + 1) * y := by
      rw [Nat.add_mul]
      omega
    refine ⟨x / y + 1, ?_⟩
    simpa [Nat.mul_comm] using heq

theorem addn1_modn_commute (x h : Nat) (_hpos : 0 < h)
    (hdiv : x / h = (x + 1) / h) :
    (x + 1) % h = x % h + 1 := by
  have hx := Nat.div_add_mod x h
  have hxs := Nat.div_add_mod (x + 1) h
  rw [← hdiv] at hxs
  omega

theorem addmod_le_mod (x y h : Nat) (hpos : 0 < h)
    (hdiv : x / h = (x + y) / h) :
    x % h + y % h < h := by
  have hx := Nat.div_add_mod x h
  have hxy := Nat.div_add_mod (x + y) h
  rw [← hdiv] at hxy
  have hry : y % h ≤ y := Nat.mod_le y h
  have hrxy : (x + y) % h < h := Nat.mod_lt (x + y) hpos
  omega

theorem divn_leq (k T x : Nat)
    (hinterval : k * T ≤ x ∧ x < (k + 1) * T) :
    x / T = k := by
  have hT : 0 < T := by
    by_contra h
    have : T = 0 := Nat.eq_zero_of_not_pos h
    subst T
    simp at hinterval
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hT).2 hinterval.2)
  · exact (Nat.le_div_iff_mul_le hT).2 hinterval.1

def div_floor (x y : Nat) : Nat := x / y

def div_ceil (x y : Nat) : Nat := if y ∣ x then x / y else x / y + 1

private theorem div_ceil_eq_ceilDiv (x y : Nat) (hy : 0 < y) :
    div_ceil x y = x ⌈/⌉ y := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  unfold div_ceil
  by_cases hdvd : y ∣ x
  · rw [if_pos hdvd]
    have hmod : x % y = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    have hx : x = y * (x / y) := by
      have := Nat.div_add_mod x y
      omega
    have hpred : y - 1 < y := by omega
    calc
      x / y = x / y + (y - 1) / y := by
        rw [Nat.div_eq_of_lt hpred, Nat.add_zero]
      _ = (y * (x / y) + (y - 1)) / y := by
        rw [Nat.mul_add_div hy]
      _ = (x + y - 1) / y := by
        congr 1
        omega
  · rw [if_neg hdvd]
    have hmod_ne : x % y ≠ 0 := by
      exact fun h => hdvd (Nat.dvd_iff_mod_eq_zero.mpr h)
    have hmod_pos : 0 < x % y := Nat.pos_of_ne_zero hmod_ne
    have hmod_lt : x % y < y := Nat.mod_lt x hy
    have hx : x = y * (x / y) + x % y :=
      (Nat.div_add_mod x y).symm
    have htail : x % y + y - 1 = y + (x % y - 1) := by omega
    have hsmall : x % y - 1 < y := by omega
    calc
      x / y + 1 = x / y + (x % y + y - 1) / y := by
        rw [htail, Nat.add_div_left (x % y - 1) hy,
          Nat.div_eq_of_lt hsmall, Nat.zero_add]
      _ = (y * (x / y) + (x % y + y - 1)) / y := by
        rw [Nat.mul_add_div hy]
      _ = (x + y - 1) / y := by
        congr 1
        omega

private theorem div_ceil_sub_add_one (a c : Nat) (hc : 0 < c)
    (hca : c ≤ a) : div_ceil a c = div_ceil (a - c) c + 1 := by
  have hdiv : a / c = (a - c) / c + 1 := Nat.div_eq_sub_div hc hca
  have hdvd : c ∣ a ↔ c ∣ a - c := by
    constructor
    · intro h
      exact Nat.dvd_sub h (dvd_refl c)
    · intro h
      have hadd : c ∣ a - c + c := dvd_add h (dvd_refl c)
      simpa [Nat.sub_add_cancel hca] using hadd
  unfold div_ceil
  by_cases ha : c ∣ a
  · have hasub : c ∣ a - c := hdvd.mp ha
    rw [if_pos ha, if_pos hasub, hdiv]
  · have hasub : ¬c ∣ a - c := fun h => ha (hdvd.mpr h)
    rw [if_neg ha, if_neg hasub, hdiv]

theorem div_ceil0 (b : Nat) : div_ceil 0 b = 0 := by
  simp [div_ceil]

theorem div_ceil_gt0 (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    0 < div_ceil a b := by
  unfold div_ceil
  by_cases hdvd : b ∣ a
  · rw [if_pos hdvd]
    exact Nat.div_pos (Nat.le_of_dvd ha hdvd) hb
  · rw [if_neg hdvd]
    simpa [Nat.add_comm] using Nat.succ_pos (a / b)

theorem div_ceil_monotone1 (d m n : Nat) (hle : m ≤ n) :
    div_ceil m d ≤ div_ceil n d := by
  by_cases hd0 : d = 0
  · subst d
    simp only [div_ceil, zero_dvd_iff, Nat.div_zero]
    split_ifs <;> omega
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    rw [div_ceil_eq_ceilDiv m d hd, div_ceil_eq_ceilDiv n d hd]
    exact (gc_mul_ceilDiv hd).monotone_l hle

theorem leq_div_ceil_add1 (delta T : Nat) (hT : 0 < T)
    (hle : T ≤ delta) :
    div_ceil (delta - T) T < div_ceil delta T := by
  rw [div_ceil_sub_add_one delta T hT hle]
  omega

theorem div_ceil_subadditive (T : Nat) :
    subadditive (fun x => div_ceil x T) := by
  intro point a b hab
  subst point
  by_cases hT0 : T = 0
  · subst T
    simp only [div_ceil, zero_dvd_iff, Nat.div_zero]
    split_ifs <;> omega
  · have hT : 0 < T := Nat.pos_of_ne_zero hT0
    change div_ceil (a + b) T ≤ div_ceil a T + div_ceil b T
    rw [div_ceil_eq_ceilDiv (a + b) T hT,
      div_ceil_eq_ceilDiv a T hT, div_ceil_eq_ceilDiv b T hT]
    apply (ceilDiv_le_iff_le_mul hT).2
    have ha : a ≤ T * (a ⌈/⌉ T) :=
      (ceilDiv_le_iff_le_mul hT).1 le_rfl
    have hb : b ≤ T * (b ⌈/⌉ T) :=
      (ceilDiv_le_iff_le_mul hT).1 le_rfl
    simpa [Nat.mul_add] using Nat.add_le_add ha hb

theorem div_ceil_multiple (delta T n : Nat) (hT : 0 < T)
    (hlt : T * n < delta) : n < div_ceil delta T := by
  rw [div_ceil_eq_ceilDiv delta T hT]
  by_contra h
  have hle : delta ⌈/⌉ T ≤ n := Nat.le_of_not_gt h
  have := (ceilDiv_le_iff_le_mul hT).1 hle
  omega

theorem div_floor_add_g (a b : Nat) (hb : 0 < b) :
    a < div_floor a b * b + b := by
  unfold div_floor
  have hdecomp : a = (a / b) * b + a % b := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod a b).symm
  have hrem := Nat.mod_lt a hb
  omega

theorem mod_elim (a b c : Nat) (hbc : b < c) :
    (a + c - b) % c =
      if b ≤ a % c then a % c - b else a % c + c - b := by
  have hc : 0 < c := lt_of_le_of_lt (Nat.zero_le b) hbc
  have hrem : a % c < c := Nat.mod_lt a hc
  split_ifs with hcase
  · have hba : b ≤ a := le_trans hcase (Nat.mod_le a c)
    have hkey : a + c - b = (a - b) + c := by omega
    rw [hkey, Nat.add_mod_right]
    conv_lhs =>
      rw [show a = c * (a / c) + a % c from (Nat.div_add_mod a c).symm]
    rw [show c * (a / c) + a % c - b =
      c * (a / c) + (a % c - b) from by omega]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · push_neg at hcase
    have hkey : a + c - b = a + (c - b) := by omega
    rw [hkey]
    conv_lhs =>
      rw [show a = c * (a / c) + a % c from (Nat.div_add_mod a c).symm]
    rw [show c * (a / c) + a % c + (c - b) =
      c * (a / c) + (a % c + (c - b)) from by omega]
    rw [Nat.mul_add_mod]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end Prosa.Util.Div_mod
