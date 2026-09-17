-- Translated from: ../rt-proofs/classic/util/div_mod.v
import Mathlib.Tactic
import Prosa.Util.Div_mod
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Div_mod

open Prosa.Util.Div_mod

theorem ltn_div_trunc (m n d : ℕ) (GT0 : d > 0) (DIV : m / d < n / d) :
    m < n := by
  have hm : m < (m / d + 1) * d := by
    have := Nat.div_add_mod m d
    have := Nat.mod_lt m GT0
    nlinarith
  have hn : n / d * d ≤ n := Nat.div_mul_le_self n d
  have : (m / d + 1) * d ≤ n / d * d := by
    apply Nat.mul_le_mul_right; omega
  omega

theorem subndiv_eq_mod (n d : ℕ) : n - n / d * d = n % d := by
  conv_lhs => rw [show n / d * d = d * (n / d) from by ring]
  have h := Nat.div_add_mod n d
  omega

theorem divSn_cases (n d : ℕ) (GT : d > 1) :
    (n / d = (n + 1) / d ∧ n % d + 1 = (n + 1) % d) ∨
    (n / d + 1 = (n + 1) / d) := by
  have hd0 : d > 0 := by omega
  have hmod_lt : n % d < d := Nat.mod_lt n hd0
  by_cases heq : n % d + 1 = d
  · right
    have hdm := Nat.div_add_mod n d
    have h1 : n + 1 = (n / d + 1) * d := by nlinarith [mul_comm d (n / d)]
    rw [h1, show (n / d + 1) * d = d * (n / d + 1) from by ring,
        Nat.mul_div_cancel_left _ hd0]
  · left
    have hlt : n % d + 1 < d := by omega
    have hdm := Nat.div_add_mod n d
    constructor
    · have : (n + 1) / d = n / d := by
        apply Nat.div_eq_of_lt_le
        · exact le_trans (Nat.div_mul_le_self n d) (Nat.le_succ n)
        · nlinarith [mul_comm d (n / d)]
      omega
    · have hdiv_eq2 : (n + 1) / d = n / d := by
        apply Nat.div_eq_of_lt_le
        · exact le_trans (Nat.div_mul_le_self n d) (Nat.le_succ n)
        · nlinarith [mul_comm d (n / d)]
      have h_n1 := Nat.div_add_mod (n + 1) d
      nlinarith [mul_comm d ((n + 1) / d), mul_comm d (n / d)]

theorem ceil_neq0 (x y : ℕ) (GEx : x > 0) (GEy : y > 0) :
    div_ceil x y > 0 := by
  unfold div_ceil
  split
  · next h =>
      obtain ⟨k, hk⟩ := h
      have hk_pos : k > 0 := by
        by_contra h0; push_neg at h0
        interval_cases k; omega
      rw [hk, Nat.mul_div_cancel_left _ GEy]
      exact hk_pos
  · next h =>
      have := Nat.zero_le (x / y)
      omega

theorem leq_divceil2r (d m n : ℕ) (GT0 : d > 0) (LE : m ≤ n) :
    div_ceil m d ≤ div_ceil n d := by
  unfold div_ceil
  split_ifs with hm hn hn
  · exact Nat.div_le_div_right LE
  · have : m / d ≤ n / d := Nat.div_le_div_right LE
    omega
  · -- d ∣ n but ¬ d ∣ m
    have hdiv_le : m / d ≤ n / d := Nat.div_le_div_right LE
    by_cases heq : m / d = n / d
    · exfalso; apply hm
      have hn_mod : n % d = 0 := Nat.dvd_iff_mod_eq_zero.mp hn
      have hm_eq := Nat.div_add_mod m d
      have hn_eq := Nat.div_add_mod n d
      have hmul_eq : d * (m / d) = d * (n / d) := by rw [heq]
      have : m % d = 0 := by omega
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    · omega
  · have : m / d ≤ n / d := Nat.div_le_div_right LE
    omega

theorem eq_modDl (p m n d : ℕ) :
    (p + m) % d = (p + n) % d ↔ m % d = n % d := by
  constructor
  · intro h
    cases d with
    | zero => simp only [Nat.mod_zero] at h ⊢; omega
    | succ d =>
      have h1 := Nat.add_mod p m (d + 1)
      have h2 := Nat.add_mod p n (d + 1)
      rw [h1, h2] at h
      set pd := p % (d + 1)
      set md := m % (d + 1)
      set nd := n % (d + 1)
      have hpd : pd < d + 1 := Nat.mod_lt p (by omega)
      have hmd : md < d + 1 := Nat.mod_lt m (by omega)
      have hnd : nd < d + 1 := Nat.mod_lt n (by omega)
      -- Case split on whether pd + md and pd + nd overflow d+1
      by_cases hm_lt : pd + md < d + 1 <;> by_cases hn_lt : pd + nd < d + 1
      · rw [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hn_lt] at h; omega
      · push_neg at hn_lt
        rw [Nat.mod_eq_of_lt hm_lt] at h
        have hrem : pd + nd - (d + 1) < d + 1 := by omega
        have hmod_n : (pd + nd) % (d + 1) = pd + nd - (d + 1) := by
          conv_lhs => rw [show pd + nd = pd + nd - (d + 1) + (d + 1) from by omega]
          rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hrem
        rw [hmod_n] at h; omega
      · push_neg at hm_lt
        rw [Nat.mod_eq_of_lt hn_lt] at h
        have hrem : pd + md - (d + 1) < d + 1 := by omega
        have hmod_m : (pd + md) % (d + 1) = pd + md - (d + 1) := by
          conv_lhs => rw [show pd + md = pd + md - (d + 1) + (d + 1) from by omega]
          rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hrem
        rw [hmod_m] at h; omega
      · push_neg at hm_lt hn_lt
        have hrem_m : pd + md - (d + 1) < d + 1 := by omega
        have hrem_n : pd + nd - (d + 1) < d + 1 := by omega
        have hmod_m : (pd + md) % (d + 1) = pd + md - (d + 1) := by
          conv_lhs => rw [show pd + md = pd + md - (d + 1) + (d + 1) from by omega]
          rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hrem_m
        have hmod_n : (pd + nd) % (d + 1) = pd + nd - (d + 1) := by
          conv_lhs => rw [show pd + nd = pd + nd - (d + 1) + (d + 1) from by omega]
          rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hrem_n
        rw [hmod_m, hmod_n] at h; omega
  · intro h
    rw [Nat.add_mod, h, ← Nat.add_mod]

theorem eq_modDr (p m n d : ℕ) :
    (m + p) % d = (n + p) % d ↔ m % d = n % d := by
  rw [show m + p = p + m from by omega, show n + p = p + n from by omega]
  exact eq_modDl p m n d

theorem modulo_exists (a b c : ℕ) (F : c > 0) (G : a % c = (b + a) % c) :
    ∃ k, b = k * c := by
  have h : (0 + a) % c = (b + a) % c := by rwa [Nat.zero_add]
  rw [eq_modDr a 0 b c] at h
  rw [Nat.zero_mod] at h
  have hmod_zero : b % c = 0 := by omega
  exact ⟨b / c, by have := Nat.div_add_mod b c; nlinarith [mul_comm c (b / c)]⟩

theorem modnS_eq (a n : ℕ) :
    (a + 1) % (n + 1) = 0 ↔ a % (n + 1) = n := by
  have hmod_n : n % (n + 1) = n := Nat.mod_eq_of_lt (by omega)
  constructor
  · intro h
    have h' : (1 + a) % (n + 1) = (1 + n) % (n + 1) := by
      rw [show 1 + a = a + 1 from by omega, h,
          show 1 + n = n + 1 from by omega, Nat.mod_self]
    rw [eq_modDl 1 a n (n + 1)] at h'
    rw [h', hmod_n]
  · intro h
    have h' : a % (n + 1) = n % (n + 1) := by rw [h, hmod_n]
    rw [← eq_modDl 1 a n (n + 1)] at h'
    rw [show 1 + a = a + 1 from by omega, show 1 + n = n + 1 from by omega] at h'
    rw [h', Nat.mod_self]

theorem modnSor' (a n : ℕ) :
    (a + 1) % n = a % n + 1 ∨ (a + 1) % n = 0 := by
  cases n with
  | zero => left; simp [Nat.mod_zero]
  | succ n =>
    have hlt : a % (n + 1) < n + 1 := Nat.mod_lt a (by omega)
    have hdiv := Nat.div_add_mod a (n + 1)
    by_cases h : a % (n + 1) + 1 < n + 1
    · left
      have hkey : a + 1 = (n + 1) * (a / (n + 1)) + (a % (n + 1) + 1) := by
        nlinarith [mul_comm (n + 1) (a / (n + 1))]
      conv_lhs => rw [hkey]
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt h
    · right
      have heq : a % (n + 1) = n := by omega
      exact (modnS_eq a n).mpr heq

theorem modnSor (a n : ℕ) :
    (a + 1) % (n + 1) = a % (n + 1) + 1 ∨ (a + 1) % (n + 1) = 0 := by
  exact modnSor' a (n + 1)

theorem modulo_cases (a c : ℕ) :
    (a + 1) % (c + 1) = a % (c + 1) + 1 ∨
    ((a + 1) % (c + 1) = 0 ∧ a % (c + 1) = c) := by
  rcases modnSor a c with h | h
  · left; exact h
  · right; exact ⟨h, (modnS_eq a c).mp h⟩

theorem ceil_eq1 (a c : ℕ) (G1 : a > 0) (G2 : a ≤ c) :
    div_ceil a c = 1 := by
  unfold div_ceil
  by_cases heq : a = c
  · subst heq
    simp [dvd_refl a, Nat.div_self G1]
  · have hlt : a < c := lt_of_le_of_ne G2 heq
    have hndvd : ¬ (c ∣ a) := by
      intro ⟨k, hk⟩
      cases k with
      | zero => omega
      | succ k =>
        have : c * (k + 1) ≥ c := Nat.le_mul_of_pos_right c (by omega)
        omega
    simp [hndvd, Nat.div_eq_of_lt hlt]

theorem ceil_suba (a c : ℕ) (G1 : c > 0) (G2 : a > c) :
    div_ceil a c = div_ceil (a - c) c + 1 := by
  unfold div_ceil
  have ha_eq : a = a - c + c := by omega
  have hac : c ≤ a := le_of_lt G2
  have hdvd_iff : c ∣ a ↔ c ∣ (a - c) := by
    constructor
    · intro h; exact Nat.dvd_sub h (dvd_refl c)
    · intro h
      have h2 : c ∣ (a - c + c) := dvd_add h (dvd_refl c)
      rwa [Nat.sub_add_cancel hac] at h2
  split_ifs with h1 h2 h2
  · -- c ∣ a, c ∣ (a - c)
    have : a / c = (a - c) / c + 1 := by
      conv_lhs => rw [ha_eq]
      exact Nat.add_div_right _ G1
    omega
  · -- c ∣ a, ¬ c ∣ (a - c)
    exact absurd (hdvd_iff.mp h1) h2
  · -- ¬ c ∣ a, c ∣ (a - c)
    exact absurd (hdvd_iff.mpr h2) h1
  · -- ¬ c ∣ a, ¬ c ∣ (a - c)
    have : a / c = (a - c) / c + 1 := by
      conv_lhs => rw [ha_eq]
      exact Nat.add_div_right _ G1
    omega

theorem mod_eq (a b : ℕ) : a % b = a - a / b * b := by
  conv_rhs => rw [show a / b * b = b * (a / b) from by ring]
  have h := Nat.div_add_mod a b
  omega

end Prosa.Classic.Util.Div_mod
