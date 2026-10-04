-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/div_mod.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 15)

import Prosa.Util.Div_mod
import Prosa.Classic.Util.Nat
import Mathlib.Data.Nat.ModEq

/-!
Division and modulo.  The source re-exports `prosa.util.div_mod` (imported above)
and declares its own `div_floor`/`div_ceil` in the classic namespace; they are
kept here with exactly the form of the accepted v0.6 definitions.

Representation notes: `m %/ d` and `m %% d` are Lean's `/` and `%` on `Nat`
(both give the same value as MathComp for `d = 0`); `y %| x` is `y ∣ x`;
`a = b %[mod d]` is `a % d = b % d`.
-/

namespace Prosa.Classic.Util.DivMod

def div_floor (x y : Nat) : Nat := x / y

def div_ceil (x y : Nat) : Nat := if y ∣ x then x / y else x / y + 1

/-- LEAN_HELPER: decomposition `n = n % d + d * (n / d)` as used below. -/
private theorem mod_add_div' (n d : Nat) : n = n % d + d * (n / d) :=
  (Nat.mod_add_div n d).symm

/-- LEAN_HELPER: for `d > 0`, the successor's remainder either increments or wraps. -/
private theorem succ_mod_cases (a d : Nat) (hd : 0 < d) :
    ((a + 1) % d = a % d + 1 ∧ a % d + 1 < d ∧ (a + 1) / d = a / d) ∨
    ((a + 1) % d = 0 ∧ a % d + 1 = d ∧ (a + 1) / d = a / d + 1) := by
  have hlt : a % d < d := Nat.mod_lt a hd
  have hdec : a + 1 = (a % d + 1) + d * (a / d) := by
    have := mod_add_div' a d; omega
  rcases Nat.lt_or_ge (a % d + 1) d with h | h
  · left
    refine ⟨?_, h, ?_⟩
    · rw [hdec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    · rw [hdec, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h, Nat.zero_add]
  · right
    have heq : a % d + 1 = d := by omega
    refine ⟨?_, heq, ?_⟩
    · rw [hdec, heq, Nat.add_mul_mod_self_left, Nat.mod_self]
    · rw [hdec, heq, Nat.add_mul_div_left _ _ hd, Nat.div_self hd, Nat.add_comm]

theorem ltn_div_trunc :
    ∀ m n d : Nat,
      0 < d →
      m / d < n / d →
      m < n := by
  intro m n d _ DIV
  by_contra h
  exact absurd (Nat.div_le_div_right (c := d) (Nat.le_of_not_lt h)) (Nat.not_le.mpr DIV)

theorem subndiv_eq_mod :
    ∀ n d : Nat, n - n / d * d = n % d := by
  intro n d
  have := mod_add_div' n d
  rw [Nat.mul_comm]
  omega

theorem divSn_cases :
    ∀ n d : Nat,
      1 < d →
      (n / d = (n + 1) / d ∧ n % d + 1 = (n + 1) % d) ∨
      (n / d + 1 = (n + 1) / d) := by
  intro n d H
  rcases succ_mod_cases n d (by omega) with ⟨h1, _, h3⟩ | ⟨_, _, h3⟩
  · exact Or.inl ⟨h3.symm, h1.symm⟩
  · exact Or.inr h3.symm

theorem ceil_neq0 :
    ∀ x y : Nat,
      0 < x →
      0 < y →
      0 < div_ceil x y := by
  intro x y GEx GEy
  unfold div_ceil
  split
  · rename_i hdvd
    exact Nat.div_pos (Nat.le_of_dvd GEx hdvd) GEy
  · exact Nat.succ_pos _

theorem leq_divceil2r :
    ∀ d m n : Nat,
      0 < d →
      m ≤ n →
      div_ceil m d ≤ div_ceil n d := by
  intro d m n GT0 LE
  have hdiv : m / d ≤ n / d := Nat.div_le_div_right LE
  unfold div_ceil
  by_cases hm : d ∣ m <;> by_cases hn : d ∣ n <;> simp only [hm, hn, ↓reduceIte]
  · exact hdiv
  · omega
  · -- `d ∤ m`, `d ∣ n`: then `m < n` and `m / d < n / d`
    have hne : m ≠ n := by rintro rfl; exact hm hn
    have hlt : m < n := Nat.lt_of_le_of_ne LE hne
    have hn' : n = n / d * d := (Nat.div_mul_cancel hn).symm
    have : m / d < n / d := by
      rw [Nat.div_lt_iff_lt_mul GT0]
      omega
    omega
  · omega

theorem eq_modDl :
    ∀ p m n d : Nat, ((p + m) % d = (p + n) % d) ↔ (m % d = n % d) := by
  intro p m n d
  exact ⟨fun G => Nat.ModEq.add_left_cancel' p G, fun G => Nat.ModEq.add_left p G⟩

theorem eq_modDr :
    ∀ p m n d : Nat, ((m + p) % d = (n + p) % d) ↔ (m % d = n % d) := by
  intro p m n d
  exact ⟨fun G => Nat.ModEq.add_right_cancel' p G, fun G => Nat.ModEq.add_right p G⟩

theorem modulo_exists :
    ∀ a b c : Nat,
      0 < c → a % c = (b + a) % c → ∃ k, b = k * c := by
  intro a b c _ G
  have G' : (0 + a) % c = (b + a) % c := by simpa using G
  have hb : 0 % c = b % c := (eq_modDr a 0 b c).mp G'
  rw [Nat.zero_mod] at hb
  exact ⟨b / c, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb.symm)).symm⟩

theorem modnS_eq :
    ∀ a n : Nat, (a + 1) % (n + 1) = 0 ↔ a % (n + 1) = n := by
  intro a n
  rcases succ_mod_cases a (n + 1) (Nat.succ_pos n) with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · constructor
    · intro h; omega
    · intro h; omega
  · constructor
    · intro _; omega
    · intro _; exact h1

theorem modnSor' :
    ∀ a n : Nat, (a + 1) % n = a % n + 1 ∨ (a + 1) % n = 0 := by
  intro a n
  cases n with
  | zero => left; simp
  | succ n =>
      rcases succ_mod_cases a (n + 1) (Nat.succ_pos n) with ⟨h1, _, _⟩ | ⟨h1, _, _⟩
      · exact Or.inl h1
      · exact Or.inr h1

theorem modnSor :
    ∀ a n : Nat, (a + 1) % (n + 1) = a % (n + 1) + 1 ∨ (a + 1) % (n + 1) = 0 := by
  intro a n
  exact modnSor' a (n + 1)

theorem modulo_cases :
    ∀ a c : Nat,
      (a + 1) % (c + 1) = a % (c + 1) + 1 ∨
        ((a + 1) % (c + 1) = 0 ∧ a % (c + 1) = c) := by
  intro a c
  rcases modnSor a c with G | G
  · exact Or.inl G
  · exact Or.inr ⟨G, (modnS_eq a c).mp G⟩

theorem ceil_eq1 :
    ∀ a c : Nat, 0 < a → a ≤ c → div_ceil a c = 1 := by
  intro a c G1 G2
  unfold div_ceil
  rcases Nat.eq_or_lt_of_le G2 with rfl | hlt
  · simp [Nat.div_self G1]
  · have hnd : ¬ c ∣ a := fun h => absurd (Nat.le_of_dvd G1 h) (Nat.not_le.mpr hlt)
    simp [hnd, Nat.div_eq_of_lt hlt]

theorem ceil_suba :
    ∀ a c : Nat, 0 < c → c < a → div_ceil a c = div_ceil (a - c) c + 1 := by
  intro a c G1 G2
  have X : a = a - c + c := by omega
  have hdvd : c ∣ a ↔ c ∣ a - c := by
    constructor
    · intro h; exact Nat.dvd_sub h (Nat.dvd_refl c)
    · intro h; rw [X]; exact Nat.dvd_add h (Nat.dvd_refl c)
  have hdiv : a / c = (a - c) / c + 1 := by
    conv_lhs => rw [X]
    exact Nat.add_div_right _ G1
  unfold div_ceil
  by_cases h : c ∣ a
  · simp [h, hdvd.mp h, hdiv]
  · have h' : ¬ c ∣ a - c := fun h' => h (hdvd.mpr h')
    simp [h, h', hdiv]

theorem mod_eq :
    ∀ a b : Nat, a % b = a - a / b * b := by
  intro a b
  exact (subndiv_eq_mod a b).symm

end Prosa.Classic.Util.DivMod
