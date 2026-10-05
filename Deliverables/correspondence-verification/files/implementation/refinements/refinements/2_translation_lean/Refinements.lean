-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/refinements.v

import Prosa.Implementation.Definitions.Task
import Prosa.Implementation.Facts.ExtrapolatedArrivalCurve
import Prosa.Util.Div_mod
import Prosa.Util.List
import Prosa.Util.Sum

/-! # Refinements library

The source imports CoqEAL 2.1.2 (`hrel`, `param`, `refinements`, `binnat`) and Rocq's binary numbers, which have
no Lean counterpart in the accepted translation.  The fragment the file (and the other `implementation/refinements`
files) uses is translated first, in this file:

* Rocq's `positive`/`N` and the Stdlib operations on them, with the same constructors and the same recursive
  algorithms (Corelib `BinNums.PosDef`/`BinNums.NatDef`, Stdlib `BinNatDef`); MathComp's `nat_of_bin`/`bin_of_nat`
  with MathComp's definitions;
* CoqEAL's `Type`-valued relations (`fun_hrel`, `hrespectful`, `refines`, the parametricity relations `bool_R`,
  `list_R`, `prod_R`), the operation classes (`zero_of`, …, `lt_of`), their `N` instances, `succN` and `Rnat`.

Representation: Rocq's cumulativity `Prop ≤ Type` is Lean's `PLift`; the source's `Type`-valued `Global
Instance`s/lemmas are Lean definitions; a Boolean `if` is Lean's `if … then … else` on a `Bool`; MathComp's `nat`
operations are Lean's (`Nat.pred`, `Nat.min`, `Nat.max`, `List.range'` for `iota`, `List.length` for `size`,
`List.all` with its arguments swapped, `List.flatten`, `List.zip`); MathComp's `last` is `seq_last`; `d %| m` is
`decide (d ∣ m)`; `\sum` and `\max` over a filtered sequence are the accepted `sumFiltered`, `sumSeq`,
`maxFiltered`. -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.Refinements

/-! ### Rocq binary numbers (Corelib `BinNums`, `BinNums.PosDef`, `BinNums.NatDef`; Stdlib `BinNatDef`)

Mirrors of the Rocq definitions the file uses, with the same constructors and the same recursive algorithms. -/

/-- Rocq `positive`: binary positive numbers, least significant bit first. -/
inductive positive : Type where
  | xI : positive → positive
  | xO : positive → positive
  | xH : positive

/-- Rocq `N`: binary natural numbers. -/
inductive N : Type where
  | N0 : N
  | Npos : positive → N

open positive N

namespace Pos

/-- Rocq `Pos.succ`. -/
def succ : positive → positive
  | xI p => xO (succ p)
  | xO p => xI p
  | xH => xO xH

mutual
/-- Rocq `Pos.add`. -/
def add : positive → positive → positive
  | xI p, xI q => xO (add_carry p q)
  | xI p, xO q => xI (add p q)
  | xI p, xH => xO (succ p)
  | xO p, xI q => xI (add p q)
  | xO p, xO q => xO (add p q)
  | xO p, xH => xI p
  | xH, xI q => xO (succ q)
  | xH, xO q => xI q
  | xH, xH => xO xH
/-- Rocq `Pos.add_carry`. -/
def add_carry : positive → positive → positive
  | xI p, xI q => xI (add_carry p q)
  | xI p, xO q => xO (add_carry p q)
  | xI p, xH => xI (succ p)
  | xO p, xI q => xO (add_carry p q)
  | xO p, xO q => xI (add p q)
  | xO p, xH => xO (succ p)
  | xH, xI q => xI (succ q)
  | xH, xO q => xO (succ q)
  | xH, xH => xI xH
end

/-- Rocq `Pos.pred_double`. -/
def pred_double : positive → positive
  | xI p => xI (xO p)
  | xO p => xI (pred_double p)
  | xH => xH

/-- Rocq `Pos.pred_N`. -/
def pred_N : positive → N
  | xI p => Npos (xO p)
  | xO p => Npos (pred_double p)
  | xH => N0

/-- Rocq `Pos.mask`. -/
inductive mask : Type where
  | IsNul : mask
  | IsPos : positive → mask
  | IsNeg : mask

open mask

/-- Rocq `Pos.succ_double_mask`. -/
def succ_double_mask : mask → mask
  | IsNul => IsPos xH
  | IsNeg => IsNeg
  | IsPos p => IsPos (xI p)

/-- Rocq `Pos.double_mask`. -/
def double_mask : mask → mask
  | IsNul => IsNul
  | IsNeg => IsNeg
  | IsPos p => IsPos (xO p)

/-- Rocq `Pos.double_pred_mask`. -/
def double_pred_mask : positive → mask
  | xI p => IsPos (xO (xO p))
  | xO p => IsPos (xO (pred_double p))
  | xH => IsNul

mutual
/-- Rocq `Pos.sub_mask` (structural on the second argument). -/
def sub_mask : positive → positive → mask
  | xI p, xI q => double_mask (sub_mask p q)
  | xI p, xO q => succ_double_mask (sub_mask p q)
  | xI p, xH => IsPos (xO p)
  | xO p, xI q => succ_double_mask (sub_mask_carry p q)
  | xO p, xO q => double_mask (sub_mask p q)
  | xO p, xH => IsPos (pred_double p)
  | xH, xH => IsNul
  | xH, _ => IsNeg
/-- Rocq `Pos.sub_mask_carry` (structural on the second argument). -/
def sub_mask_carry : positive → positive → mask
  | xI p, xI q => succ_double_mask (sub_mask_carry p q)
  | xI p, xO q => double_mask (sub_mask p q)
  | xI p, xH => IsPos (pred_double p)
  | xO p, xI q => double_mask (sub_mask_carry p q)
  | xO p, xO q => succ_double_mask (sub_mask_carry p q)
  | xO p, xH => double_pred_mask p
  | xH, _ => IsNeg
end

/-- Rocq `Pos.mul`. -/
def mul : positive → positive → positive
  | xI p, y => add y (xO (mul p y))
  | xO p, y => xO (mul p y)
  | xH, y => y

/-- Rocq `Pos.compare_cont` (Rocq `comparison` is Lean `Ordering`). -/
def compare_cont : Ordering → positive → positive → Ordering
  | r, xI p, xI q => compare_cont r p q
  | _, xI p, xO q => compare_cont .gt p q
  | _, xI _, xH => .gt
  | _, xO p, xI q => compare_cont .lt p q
  | r, xO p, xO q => compare_cont r p q
  | _, xO _, xH => .gt
  | _, xH, xI _ => .lt
  | _, xH, xO _ => .lt
  | r, xH, xH => r

/-- Rocq `Pos.compare`. -/
def compare : positive → positive → Ordering := compare_cont .eq

/-- Rocq `Pos.eqb`. -/
def eqb : positive → positive → Bool
  | xI p, xI q => eqb p q
  | xO p, xO q => eqb p q
  | xH, xH => true
  | _, _ => false

end Pos

namespace N

/-- Rocq `N.succ_double`. -/
def succ_double : N → N
  | N0 => Npos xH
  | Npos p => Npos (xI p)

/-- Rocq `N.double`. -/
def double : N → N
  | N0 => N0
  | Npos p => Npos (xO p)

/-- Rocq `N.sub`. -/
def sub : N → N → N
  | N0, _ => N0
  | n, N0 => n
  | Npos n', Npos m' =>
      match Pos.sub_mask n' m' with
      | .IsPos p => Npos p
      | _ => N0

/-- Rocq `N.compare`. -/
def compare : N → N → Ordering
  | N0, N0 => .eq
  | N0, Npos _ => .lt
  | Npos _, N0 => .gt
  | Npos n', Npos m' => Pos.compare n' m'

/-- Rocq `N.leb`. -/
def leb (x y : N) : Bool :=
  match compare x y with
  | .gt => false
  | _ => true

/-- Rocq `N.pos_div_eucl`. -/
def pos_div_eucl : positive → N → N × N
  | xH, b =>
      match b with
      | Npos xH => (Npos xH, N0)
      | _ => (N0, Npos xH)
  | xO a', b =>
      match pos_div_eucl a' b with
      | (q, r) =>
        let r' := double r
        if leb b r' then (succ_double q, sub r' b) else (double q, r')
  | xI a', b =>
      match pos_div_eucl a' b with
      | (q, r) =>
        let r' := succ_double r
        if leb b r' then (succ_double q, sub r' b) else (double q, r')

/-- Rocq `N.zero`. -/
def zero : N := N0

/-- Rocq `N.one`. -/
def one : N := Npos xH

/-- Rocq `N.succ`. -/
def succ : N → N
  | N0 => Npos xH
  | Npos p => Npos (Pos.succ p)

/-- Rocq `N.add`. -/
def add : N → N → N
  | N0, m => m
  | n, N0 => n
  | Npos p, Npos q => Npos (Pos.add p q)

/-- Rocq `N.mul`. -/
def mul : N → N → N
  | N0, _ => N0
  | _, N0 => N0
  | Npos p, Npos q => Npos (Pos.mul p q)

/-- Rocq `N.eqb`. -/
def eqb : N → N → Bool
  | N0, N0 => true
  | Npos p, Npos q => Pos.eqb p q
  | _, _ => false

/-- Rocq `N.ltb`. -/
def ltb (x y : N) : Bool :=
  match compare x y with
  | .lt => true
  | _ => false

/-- Rocq `N.div_eucl`. -/
def div_eucl : N → N → N × N
  | N0, _ => (N0, N0)
  | a, N0 => (N0, a)
  | Npos na, b => pos_div_eucl na b

/-- Rocq `N.div`. -/
def div (a b : N) : N := (div_eucl a b).1

/-- Rocq `N.modulo`. -/
def modulo (a b : N) : N := (div_eucl a b).2

end N

/-! ### MathComp `ssrnat`: the coercion between `N` and `nat` -/

namespace NatTrec

/-- MathComp `NatTrec.add` (tail-recursive addition). -/
def add : Nat → Nat → Nat
  | 0, n => n
  | Nat.succ m', n => add m' (Nat.succ n)

/-- MathComp `NatTrec.double`. -/
def double : Nat → Nat
  | 0 => 0
  | Nat.succ n' => add n' (Nat.succ (Nat.succ n'))

end NatTrec

/-- MathComp `nat_of_pos`. -/
def nat_of_pos : positive → Nat
  | xO p => NatTrec.double (nat_of_pos p)
  | xI p => Nat.succ (NatTrec.double (nat_of_pos p))
  | xH => 1

/-- MathComp `nat_of_bin` (the coercion `N >-> nat`). -/
def nat_of_bin : N → Nat
  | Npos p => nat_of_pos p
  | N0 => 0

/-- MathComp `pos_of_nat`. -/
def pos_of_nat : Nat → Nat → positive
  | Nat.succ n, Nat.succ (Nat.succ m) => pos_of_nat n m
  | Nat.succ n, 1 => xO (pos_of_nat n n)
  | Nat.succ n, 0 => xI (pos_of_nat n n)
  | 0, _ => xH

/-- MathComp `bin_of_nat`. -/
def bin_of_nat : Nat → N
  | Nat.succ n => Npos (pos_of_nat n n)
  | 0 => N0

/-! #### Arithmetic of the binary numbers (Lean proofs; facts the Rocq side takes from Stdlib and MathComp) -/

theorem NatTrec_add_eq (m n : Nat) : NatTrec.add m n = m + n := by
  induction m generalizing n with
  | zero => simp [NatTrec.add]
  | succ m ih => simp only [NatTrec.add, ih]; omega

theorem NatTrec_double_eq (n : Nat) : NatTrec.double n = 2 * n := by
  cases n with
  | zero => rfl
  | succ n => simp only [NatTrec.double, NatTrec_add_eq]; omega

theorem nat_of_pos_xI (p : positive) : nat_of_pos (xI p) = 2 * nat_of_pos p + 1 := by
  simp [nat_of_pos, NatTrec_double_eq]

theorem nat_of_pos_xO (p : positive) : nat_of_pos (xO p) = 2 * nat_of_pos p := by
  simp [nat_of_pos, NatTrec_double_eq]

theorem nat_of_pos_xH : nat_of_pos xH = 1 := rfl

theorem nat_of_pos_pos (p : positive) : 0 < nat_of_pos p := by
  induction p with
  | xI p ih => rw [nat_of_pos_xI]; omega
  | xO p ih => rw [nat_of_pos_xO]; omega
  | xH => rw [nat_of_pos_xH]; omega

theorem nat_of_pos_succ (p : positive) : nat_of_pos (Pos.succ p) = nat_of_pos p + 1 := by
  induction p with
  | xI p ih => simp only [Pos.succ, nat_of_pos_xO, nat_of_pos_xI, ih]; omega
  | xO p ih => simp only [Pos.succ, nat_of_pos_xO, nat_of_pos_xI]
  | xH => rfl

theorem nat_of_pos_add (p q : positive) :
    nat_of_pos (Pos.add p q) = nat_of_pos p + nat_of_pos q ∧
    nat_of_pos (Pos.add_carry p q) = nat_of_pos p + nat_of_pos q + 1 := by
  induction p generalizing q with
  | xI p ih =>
    have h1 := fun q => (ih q).1
    have h2 := fun q => (ih q).2
    cases q <;> refine ⟨?_, ?_⟩ <;>
      simp only [Pos.add, Pos.add_carry, nat_of_pos_xO, nat_of_pos_xI, nat_of_pos_xH, nat_of_pos_succ,
        h1, h2] <;> omega
  | xO p ih =>
    have h1 := fun q => (ih q).1
    have h2 := fun q => (ih q).2
    cases q <;> refine ⟨?_, ?_⟩ <;>
      simp only [Pos.add, Pos.add_carry, nat_of_pos_xO, nat_of_pos_xI, nat_of_pos_xH, nat_of_pos_succ,
        h1, h2] <;> omega
  | xH =>
    cases q <;> refine ⟨?_, ?_⟩ <;>
      simp only [Pos.add, Pos.add_carry, nat_of_pos_xO, nat_of_pos_xI, nat_of_pos_xH, nat_of_pos_succ] <;>
      omega

theorem nat_of_pos_pred_double (p : positive) :
    nat_of_pos (Pos.pred_double p) = 2 * nat_of_pos p - 1 := by
  induction p with
  | xI p ih => simp only [Pos.pred_double, nat_of_pos_xO, nat_of_pos_xI]; omega
  | xO p ih =>
    have := nat_of_pos_pos p
    simp only [Pos.pred_double, nat_of_pos_xO, nat_of_pos_xI, ih]; omega
  | xH => rfl

theorem nat_of_bin_pred_N (p : positive) :
    nat_of_bin (Pos.pred_N p) = nat_of_pos p - 1 := by
  cases p with
  | xI p => simp only [Pos.pred_N, nat_of_bin, nat_of_pos_xO, nat_of_pos_xI]; omega
  | xO p => simp only [Pos.pred_N, nat_of_bin, nat_of_pos_pred_double, nat_of_pos_xO]
  | xH => rfl

/-- Meaning of a subtraction mask: `IsNul` is `0`, `IsPos p` is `p`, `IsNeg` is "negative". -/
def mask_val : Pos.mask → Option Nat
  | .IsNul => some 0
  | .IsPos p => some (nat_of_pos p)
  | .IsNeg => none

theorem mask_val_succ_double (m : Pos.mask) :
    mask_val (Pos.succ_double_mask m) = (mask_val m).map (fun v => 2 * v + 1) := by
  cases m <;> simp [Pos.succ_double_mask, mask_val, nat_of_pos_xI, nat_of_pos_xH]

theorem mask_val_double (m : Pos.mask) :
    mask_val (Pos.double_mask m) = (mask_val m).map (fun v => 2 * v) := by
  cases m <;> simp [Pos.double_mask, mask_val, nat_of_pos_xO]

theorem mask_val_sub (p q : positive) :
    mask_val (Pos.sub_mask p q) =
      (if nat_of_pos q ≤ nat_of_pos p then some (nat_of_pos p - nat_of_pos q) else none) ∧
    mask_val (Pos.sub_mask_carry p q) =
      (if nat_of_pos q + 1 ≤ nat_of_pos p then some (nat_of_pos p - nat_of_pos q - 1) else none) := by
  induction q generalizing p with
  | xI q ih =>
    have hq := nat_of_pos_pos q
    have h1 := fun p => (ih p).1
    have h2 := fun p => (ih p).2
    cases p with
    | xI p | xO p =>
      have := nat_of_pos_pos p
      refine ⟨?_, ?_⟩ <;>
        simp only [Pos.sub_mask, Pos.sub_mask_carry, mask_val_double, mask_val_succ_double, h1, h2,
          nat_of_pos_xI, nat_of_pos_xO] <;> split_ifs <;> (try simp) <;> omega
    | xH =>
      refine ⟨?_, ?_⟩ <;>
        simp only [Pos.sub_mask, Pos.sub_mask_carry, mask_val, nat_of_pos_xI, nat_of_pos_xH] <;>
        split_ifs <;> (try simp) <;> omega
  | xO q ih =>
    have hq := nat_of_pos_pos q
    have h1 := fun p => (ih p).1
    have h2 := fun p => (ih p).2
    cases p with
    | xI p | xO p =>
      have := nat_of_pos_pos p
      refine ⟨?_, ?_⟩ <;>
        simp only [Pos.sub_mask, Pos.sub_mask_carry, mask_val_double, mask_val_succ_double, h1, h2,
          nat_of_pos_xI, nat_of_pos_xO] <;> split_ifs <;> (try simp) <;> omega
    | xH =>
      refine ⟨?_, ?_⟩ <;>
        simp only [Pos.sub_mask, Pos.sub_mask_carry, mask_val, nat_of_pos_xO, nat_of_pos_xH] <;>
        split_ifs <;> (try simp) <;> omega
  | xH =>
    cases p with
    | xI p =>
      have := nat_of_pos_pos p
      refine ⟨?_, ?_⟩ <;>
        simp only [Pos.sub_mask, Pos.sub_mask_carry, mask_val, nat_of_pos_xI, nat_of_pos_xO,
          nat_of_pos_xH, nat_of_pos_pred_double] <;> split_ifs <;> (try simp) <;> omega
    | xO p =>
      have := nat_of_pos_pos p
      cases p with
      | xI p | xO p =>
        have := nat_of_pos_pos p
        refine ⟨?_, ?_⟩ <;>
          simp only [Pos.sub_mask, Pos.sub_mask_carry, Pos.double_pred_mask, mask_val, nat_of_pos_xI,
            nat_of_pos_xO, nat_of_pos_xH, nat_of_pos_pred_double] <;> split_ifs <;> (try simp) <;> omega
      | xH =>
        refine ⟨?_, ?_⟩ <;>
          simp only [Pos.sub_mask, Pos.sub_mask_carry, Pos.double_pred_mask, mask_val, nat_of_pos_xO,
            nat_of_pos_xH, nat_of_pos_pred_double] <;> split_ifs <;> (try simp) <;> omega
    | xH =>
      refine ⟨?_, ?_⟩ <;>
        simp only [Pos.sub_mask, Pos.sub_mask_carry, mask_val, nat_of_pos_xH] <;>
        split_ifs <;> (try simp) <;> omega

theorem nat_of_bin_sub (a b : N) : nat_of_bin (N.sub a b) = nat_of_bin a - nat_of_bin b := by
  cases a with
  | N0 => simp [N.sub, nat_of_bin]
  | Npos p =>
    cases b with
    | N0 => simp [N.sub, nat_of_bin]
    | Npos q =>
      have h := (mask_val_sub p q).1
      simp only [N.sub, nat_of_bin]
      cases hm : Pos.sub_mask p q with
      | IsNul =>
        rw [hm] at h; simp only [mask_val] at h
        split_ifs at h with hc <;> simp at h; omega
      | IsPos r =>
        rw [hm] at h; simp only [mask_val] at h
        split_ifs at h with hc <;> simp at h; exact h
      | IsNeg =>
        rw [hm] at h; simp only [mask_val] at h
        split_ifs at h with hc <;> simp at h; simp <;> omega

theorem nat_of_pos_mul (p q : positive) : nat_of_pos (Pos.mul p q) = nat_of_pos p * nat_of_pos q := by
  induction p with
  | xI p ih => simp only [Pos.mul, (nat_of_pos_add _ _).1, nat_of_pos_xO, nat_of_pos_xI, ih]; ring
  | xO p ih => simp only [Pos.mul, nat_of_pos_xO, ih]; ring
  | xH => simp [Pos.mul, nat_of_pos_xH]

theorem compare_cont_spec (r : Ordering) (p q : positive) :
    Pos.compare_cont r p q =
      if nat_of_pos p < nat_of_pos q then .lt
      else if nat_of_pos q < nat_of_pos p then .gt else r := by
  induction p generalizing r q with
  | xI p ih =>
    cases q with
    | xI q => simp only [Pos.compare_cont, ih, nat_of_pos_xI]; split_ifs <;> first | rfl | omega
    | xO q => simp only [Pos.compare_cont, ih, nat_of_pos_xI, nat_of_pos_xO]; split_ifs <;> first | rfl | omega
    | xH =>
      have := nat_of_pos_pos p
      simp only [Pos.compare_cont, nat_of_pos_xI, nat_of_pos_xH]; split_ifs <;> first | rfl | omega
  | xO p ih =>
    have := nat_of_pos_pos p
    cases q with
    | xI q => simp only [Pos.compare_cont, ih, nat_of_pos_xI, nat_of_pos_xO]; split_ifs <;> first | rfl | omega
    | xO q => simp only [Pos.compare_cont, ih, nat_of_pos_xO]; split_ifs <;> first | rfl | omega
    | xH => simp only [Pos.compare_cont, nat_of_pos_xO, nat_of_pos_xH]; split_ifs <;> first | rfl | omega
  | xH =>
    cases q with
    | xI q =>
      have := nat_of_pos_pos q
      simp only [Pos.compare_cont, nat_of_pos_xI, nat_of_pos_xH]; split_ifs <;> first | rfl | omega
    | xO q =>
      have := nat_of_pos_pos q
      simp only [Pos.compare_cont, nat_of_pos_xO, nat_of_pos_xH]; split_ifs <;> first | rfl | omega
    | xH => simp [Pos.compare_cont, nat_of_pos_xH]

theorem N_compare_spec (a b : N) :
    N.compare a b =
      if nat_of_bin a < nat_of_bin b then .lt
      else if nat_of_bin b < nat_of_bin a then .gt else .eq := by
  cases a with
  | N0 =>
    cases b with
    | N0 => rfl
    | Npos q =>
      have h : nat_of_bin N0 < nat_of_bin (Npos q) := nat_of_pos_pos q
      simp only [N.compare, if_pos h]
  | Npos p =>
    have := nat_of_pos_pos p
    cases b with
    | N0 =>
      have h1 : ¬ nat_of_bin (Npos p) < nat_of_bin N0 := by simp [nat_of_bin]
      have h2 : nat_of_bin N0 < nat_of_bin (Npos p) := this
      simp only [N.compare, if_neg h1, if_pos h2]
    | Npos q => exact compare_cont_spec .eq p q

theorem N_leb_spec (a b : N) : N.leb a b = decide (nat_of_bin a ≤ nat_of_bin b) := by
  simp only [N.leb, N_compare_spec]; split_ifs <;> (try simp) <;> omega

theorem N_ltb_spec (a b : N) : N.ltb a b = decide (nat_of_bin a < nat_of_bin b) := by
  simp only [N.ltb, N_compare_spec]; split_ifs <;> (try simp) <;> omega

theorem nat_of_pos_inj (p q : positive) (h : nat_of_pos p = nat_of_pos q) : p = q := by
  induction p generalizing q with
  | xI p ih =>
    cases q with
    | xI q => rw [nat_of_pos_xI, nat_of_pos_xI] at h; rw [ih q (by omega)]
    | xO q => rw [nat_of_pos_xI, nat_of_pos_xO] at h; omega
    | xH => have := nat_of_pos_pos p; rw [nat_of_pos_xI, nat_of_pos_xH] at h; omega
  | xO p ih =>
    have := nat_of_pos_pos p
    cases q with
    | xI q => rw [nat_of_pos_xI, nat_of_pos_xO] at h; omega
    | xO q => rw [nat_of_pos_xO, nat_of_pos_xO] at h; rw [ih q (by omega)]
    | xH => rw [nat_of_pos_xO, nat_of_pos_xH] at h; omega
  | xH =>
    cases q with
    | xI q => have := nat_of_pos_pos q; rw [nat_of_pos_xI, nat_of_pos_xH] at h; omega
    | xO q => have := nat_of_pos_pos q; rw [nat_of_pos_xO, nat_of_pos_xH] at h; omega
    | xH => rfl

theorem Pos_eqb_spec (p q : positive) : Pos.eqb p q = decide (nat_of_pos p = nat_of_pos q) := by
  induction p generalizing q with
  | xI p ih =>
    cases q with
    | xI q => simp only [Pos.eqb, ih, nat_of_pos_xI]; simp only [decide_eq_decide]; omega
    | xO q => simp only [Pos.eqb, nat_of_pos_xI, nat_of_pos_xO]; simp <;> omega
    | xH => have := nat_of_pos_pos p; simp only [Pos.eqb, nat_of_pos_xI, nat_of_pos_xH]; simp <;> omega
  | xO p ih =>
    have := nat_of_pos_pos p
    cases q with
    | xI q => simp only [Pos.eqb, nat_of_pos_xI, nat_of_pos_xO]; simp <;> omega
    | xO q => simp only [Pos.eqb, ih, nat_of_pos_xO]; simp only [decide_eq_decide]; omega
    | xH => simp only [Pos.eqb, nat_of_pos_xO, nat_of_pos_xH]; simp <;> omega
  | xH =>
    cases q with
    | xI q => have := nat_of_pos_pos q; simp only [Pos.eqb, nat_of_pos_xI, nat_of_pos_xH]; simp <;> omega
    | xO q => have := nat_of_pos_pos q; simp only [Pos.eqb, nat_of_pos_xO, nat_of_pos_xH]; simp <;> omega
    | xH => rfl

theorem N_eqb_spec (a b : N) : N.eqb a b = decide (nat_of_bin a = nat_of_bin b) := by
  cases a with
  | N0 =>
    cases b with
    | N0 => rfl
    | Npos q =>
      have := nat_of_pos_pos q
      simp only [N.eqb, nat_of_bin]; exact (decide_eq_false (by omega)).symm
  | Npos p =>
    have := nat_of_pos_pos p
    cases b with
    | N0 => simp only [N.eqb, nat_of_bin]; exact (decide_eq_false (by omega)).symm
    | Npos q => exact Pos_eqb_spec p q

theorem nat_of_bin_succ_double (a : N) : nat_of_bin (N.succ_double a) = 2 * nat_of_bin a + 1 := by
  cases a <;> simp [N.succ_double, nat_of_bin, nat_of_pos_xI, nat_of_pos_xH]

theorem nat_of_bin_double (a : N) : nat_of_bin (N.double a) = 2 * nat_of_bin a := by
  cases a <;> simp [N.double, nat_of_bin, nat_of_pos_xO]

/-- One step of the binary long division: from the quotient and remainder of `a` by `b`,
those of `2 * a + c` (`c ≤ 1`). -/
theorem div_mod_step (a b c q r : Nat) (hb : 0 < b) (hc : c ≤ 1) (hq : q = a / b) (hr : r = a % b) :
    (b ≤ 2 * r + c → (2 * a + c) / b = 2 * q + 1 ∧ (2 * a + c) % b = 2 * r + c - b) ∧
    (¬ b ≤ 2 * r + c → (2 * a + c) / b = 2 * q ∧ (2 * a + c) % b = 2 * r + c) := by
  have hdm := Nat.mod_add_div a b
  have hlt := Nat.mod_lt a hb
  rw [← hq, ← hr] at hdm
  rw [← hr] at hlt
  have e1 : b * (2 * q + 1) = 2 * (b * q) + b := by ring
  have e2 : b * (2 * q) = 2 * (b * q) := by ring
  constructor
  · intro hle
    rw [Nat.div_mod_unique hb, e1]
    omega
  · intro hle
    rw [Nat.div_mod_unique hb, e2]
    omega

theorem pos_div_eucl_spec (a : positive) (b : N) (hb : 0 < nat_of_bin b) :
    nat_of_bin (N.pos_div_eucl a b).1 = nat_of_pos a / nat_of_bin b ∧
    nat_of_bin (N.pos_div_eucl a b).2 = nat_of_pos a % nat_of_bin b := by
  induction a with
  | xH =>
    cases b with
    | N0 => simp [nat_of_bin] at hb
    | Npos q =>
      cases q with
      | xH => simp [N.pos_div_eucl, nat_of_bin, nat_of_pos_xH]
      | xI q =>
        have := nat_of_pos_pos q
        simp only [N.pos_div_eucl, nat_of_bin, nat_of_pos_xH, nat_of_pos_xI]
        exact ⟨(Nat.div_eq_of_lt (by omega)).symm, (Nat.mod_eq_of_lt (by omega)).symm⟩
      | xO q =>
        have := nat_of_pos_pos q
        simp only [N.pos_div_eucl, nat_of_bin, nat_of_pos_xH, nat_of_pos_xO]
        exact ⟨(Nat.div_eq_of_lt (by omega)).symm, (Nat.mod_eq_of_lt (by omega)).symm⟩
  | xO a ih =>
    obtain ⟨hq, hr⟩ := ih
    simp only [N.pos_div_eucl]
    generalize N.pos_div_eucl a b = qr at hq hr
    obtain ⟨q, r⟩ := qr
    simp only at hq hr ⊢
    have step := div_mod_step (nat_of_pos a) (nat_of_bin b) 0 _ _ hb (by omega) hq hr
    rw [nat_of_pos_xO]
    split_ifs with hle
    · rw [N_leb_spec, nat_of_bin_double] at hle
      simp only [decide_eq_true_eq] at hle
      rw [nat_of_bin_succ_double, nat_of_bin_sub, nat_of_bin_double]
      have h := step.1 (by omega)
      simp only [Nat.add_zero] at h
      exact ⟨h.1.symm, h.2.symm⟩
    · rw [N_leb_spec, nat_of_bin_double] at hle
      simp only [decide_eq_true_eq] at hle
      rw [nat_of_bin_double, nat_of_bin_double]
      have h := step.2 (by omega)
      simp only [Nat.add_zero] at h
      exact ⟨h.1.symm, h.2.symm⟩
  | xI a ih =>
    obtain ⟨hq, hr⟩ := ih
    simp only [N.pos_div_eucl]
    generalize N.pos_div_eucl a b = qr at hq hr
    obtain ⟨q, r⟩ := qr
    simp only at hq hr ⊢
    have step := div_mod_step (nat_of_pos a) (nat_of_bin b) 1 _ _ hb (by omega) hq hr
    rw [nat_of_pos_xI]
    split_ifs with hle
    · rw [N_leb_spec, nat_of_bin_succ_double] at hle
      simp only [decide_eq_true_eq] at hle
      rw [nat_of_bin_succ_double, nat_of_bin_sub, nat_of_bin_succ_double]
      exact ⟨(step.1 hle).1.symm, (step.1 hle).2.symm⟩
    · rw [N_leb_spec, nat_of_bin_succ_double] at hle
      simp only [decide_eq_true_eq] at hle
      rw [nat_of_bin_double, nat_of_bin_succ_double]
      exact ⟨(step.2 hle).1.symm, (step.2 hle).2.symm⟩

theorem nat_of_bin_div_mod (a b : N) :
    nat_of_bin (N.div a b) = nat_of_bin a / nat_of_bin b ∧
    nat_of_bin (N.modulo a b) = nat_of_bin a % nat_of_bin b := by
  cases a with
  | N0 => simp [N.div, N.modulo, N.div_eucl, nat_of_bin]
  | Npos p =>
    cases b with
    | N0 => simp [N.div, N.modulo, N.div_eucl, nat_of_bin]
    | Npos q =>
      have := nat_of_pos_pos q
      exact pos_div_eucl_spec p (Npos q) (by simpa [nat_of_bin] using this)

theorem nat_of_bin_succ (a : N) : nat_of_bin (N.succ a) = nat_of_bin a + 1 := by
  cases a <;> simp [N.succ, nat_of_bin, nat_of_pos_succ, nat_of_pos_xH]

theorem nat_of_bin_add (a b : N) : nat_of_bin (N.add a b) = nat_of_bin a + nat_of_bin b := by
  cases a <;> cases b <;> simp [N.add, nat_of_bin, (nat_of_pos_add _ _).1]

theorem nat_of_bin_mul (a b : N) : nat_of_bin (N.mul a b) = nat_of_bin a * nat_of_bin b := by
  cases a <;> cases b <;> simp [N.mul, nat_of_bin, nat_of_pos_mul]

theorem nat_of_bin_inj (a b : N) (h : nat_of_bin a = nat_of_bin b) : a = b := by
  cases a with
  | N0 =>
    cases b with
    | N0 => rfl
    | Npos q => have := nat_of_pos_pos q; simp [nat_of_bin] at h; omega
  | Npos p =>
    cases b with
    | N0 => have := nat_of_pos_pos p; simp [nat_of_bin] at h; omega
    | Npos q => rw [nat_of_pos_inj p q h]

theorem nat_of_pos_of_nat (n m : Nat) (h : m ≤ n) : nat_of_pos (pos_of_nat n m) = 2 * n - m + 1 := by
  induction n generalizing m with
  | zero => simp [pos_of_nat, nat_of_pos_xH]
  | succ n ih =>
    match m, h with
    | 0, _ => simp only [pos_of_nat, nat_of_pos_xI, ih n (le_refl n)]; omega
    | 1, _ => simp only [pos_of_nat, nat_of_pos_xO, ih n (le_refl n)]; omega
    | Nat.succ (Nat.succ m), h => simp only [pos_of_nat, ih m (by omega)]; omega

theorem bin_of_natK (n : Nat) : nat_of_bin (bin_of_nat n) = n := by
  cases n with
  | zero => rfl
  | succ n => simp only [bin_of_nat, nat_of_bin, nat_of_pos_of_nat n n (le_refl n)]; omega

theorem nat_of_binK (a : N) : bin_of_nat (nat_of_bin a) = a :=
  nat_of_bin_inj _ _ (bin_of_natK _)


/-! ### CoqEAL 2.1.2: the fragment of `hrel`, `param`, `refinements` and `binnat` the file uses

CoqEAL's relations are `Type`-valued (`A -> B -> Type`); Rocq's cumulativity lets a `Prop` (such as an
equation) stand where a `Type` is expected.  Lean has no cumulativity from `Prop` to `Type`: such a `Prop` is
wrapped in `PLift`. -/

/-- CoqEAL `fun_hrel`: the graph of `f` as a type-valued relation (`f b = a`). -/
def fun_hrel {A B : Type} (f : B → A) : A → B → Type := fun a b => PLift (f b = a)

/-- CoqEAL `hrespectful` (CoqEAL notation `R ==> R'`). -/
def hrespectful {A B C D : Type} (R : A → B → Type) (R' : C → D → Type) :
    (A → C) → (B → D) → Type :=
  fun f g => ∀ (x : A) (y : B), R x y → R' (f x) (g y)

/-- CoqEAL `refines`: the class of refinement relations (CoqEAL locks `R` behind `refines_key`, which only
controls unfolding). -/
class refines {A B : Type} (R : A → B → Type) (m : A) (n : B) : Type where
  refines_rel : R m n

/-- CoqEAL `unify`: a `Prop`-valued class. -/
def unify {A : Type} (x y : A) : Prop := x = y

/-- The `bool_R` parametricity relation of CoqEAL `param` (generated by elpi `derive.param2`). -/
inductive bool_R : Bool → Bool → Type where
  | true_R : bool_R true true
  | false_R : bool_R false false

/-- The `list_R` parametricity relation of CoqEAL `param`. -/
inductive list_R {A1 A2 : Type} (A_R : A1 → A2 → Type) : List A1 → List A2 → Type where
  | nil_R : list_R A_R [] []
  | cons_R : ∀ {x1 : A1} {x2 : A2}, A_R x1 x2 → ∀ {s1 : List A1} {s2 : List A2},
      list_R A_R s1 s2 → list_R A_R (x1 :: s1) (x2 :: s2)

/-- The `prod_R` parametricity relation of CoqEAL `param`. -/
inductive prod_R {A1 A2 : Type} (A_R : A1 → A2 → Type) {B1 B2 : Type} (B_R : B1 → B2 → Type) :
    A1 × B1 → A2 × B2 → Type where
  | pair_R : ∀ {a1 : A1} {a2 : A2}, A_R a1 a2 → ∀ {b1 : B1} {b2 : B2}, B_R b1 b2 →
      prod_R A_R B_R (a1, b1) (a2, b2)

/-- CoqEAL `zero_of` (a definitional class in Rocq: `zero_of A` is `A`). -/
class zero_of (A : Type) where
  zero_op : A
/-- CoqEAL `one_of`. -/
class one_of (A : Type) where
  one_op : A
/-- CoqEAL `add_of`. -/
class add_of (A : Type) where
  add_op : A → A → A
/-- CoqEAL `sub_of`. -/
class sub_of (A : Type) where
  sub_op : A → A → A
/-- CoqEAL `mul_of`. -/
class mul_of (A : Type) where
  mul_op : A → A → A
/-- CoqEAL `div_of`. -/
class div_of (A : Type) where
  div_op : A → A → A
/-- CoqEAL `mod_of`. -/
class mod_of (A : Type) where
  mod_op : A → A → A
/-- CoqEAL `eq_of`. -/
class eq_of (A : Type) where
  eq_op : A → A → Bool
/-- CoqEAL `leq_of`. -/
class leq_of (A : Type) where
  leq_op : A → A → Bool
/-- CoqEAL `lt_of`. -/
class lt_of (A : Type) where
  lt_op : A → A → Bool

export zero_of (zero_op)
export one_of (one_op)
export add_of (add_op)
export sub_of (sub_op)
export mul_of (mul_op)
export div_of (div_op)
export mod_of (mod_op)
export eq_of (eq_op)
export leq_of (leq_op)
export lt_of (lt_op)

/-- CoqEAL `binnat`: the operations on `N`. -/
instance zero_N : zero_of N := ⟨N.zero⟩
instance one_N : one_of N := ⟨N.one⟩
instance add_N : add_of N := ⟨N.add⟩

/-- CoqEAL `succN`. -/
def succN (n : N) : N := add_op one_op n

instance sub_N : sub_of N := ⟨N.sub⟩
instance mul_N : mul_of N := ⟨N.mul⟩
instance div_N : div_of N := ⟨N.div⟩
instance mod_N : mod_of N := ⟨N.modulo⟩
instance eq_N : eq_of N := ⟨N.eqb⟩
instance leq_N : leq_of N := ⟨N.leb⟩
instance lt_N : lt_of N := ⟨N.ltb⟩

/-- CoqEAL `Rnat`: a unary number and a binary number denote the same natural number. -/
def Rnat : Nat → N → Type := fun_hrel nat_of_bin

/-! #### Basic facts on the CoqEAL fragment (Lean proofs) -/

theorem Rnat_eq {n : Nat} {x : N} (h : Rnat n x) : nat_of_bin x = n := h.down

def Rnat_intro {n : Nat} {x : N} (h : nat_of_bin x = n) : Rnat n x := ⟨h⟩

def bool_R_of_eq {b b' : Bool} (h : b = b') : bool_R b b' := by
  subst h; cases b
  · exact .false_R
  · exact .true_R

theorem bool_R_eq {b b' : Bool} (h : bool_R b b') : b = b' := by
  cases h <;> rfl

theorem list_R_Rnat_eq {xs : List Nat} {ys : List N} (h : list_R Rnat xs ys) :
    ys.map nat_of_bin = xs := by
  induction h with
  | nil_R => rfl
  | cons_R hx _ ih => simp [Rnat_eq hx, ih]

def list_R_Rnat_of_eq : ∀ (ys : List N), list_R Rnat (ys.map nat_of_bin) ys
  | [] => .nil_R
  | y :: ys => .cons_R (Rnat_intro rfl) (list_R_Rnat_of_eq ys)

def list_R_map {A A' B B' : Type} {rA : A → A' → Type} {rB : B → B' → Type} {F : A → B} {F' : A' → B'}
    (hF : ∀ x x', rA x x' → rB (F x) (F' x')) :
    ∀ {xs : List A} {xs' : List A'}, list_R rA xs xs' → list_R rB (xs.map F) (xs'.map F')
  | _, _, .nil_R => .nil_R
  | _, _, .cons_R hx hs => .cons_R (hF _ _ hx) (list_R_map hF hs)

def list_R_filter {A A' : Type} {rA : A → A' → Type} {P : A → Bool} {P' : A' → Bool}
    (hP : ∀ x x', rA x x' → P x = P' x') :
    ∀ {xs : List A} {xs' : List A'}, list_R rA xs xs' → list_R rA (xs.filter P) (xs'.filter P')
  | _, _, .nil_R => .nil_R
  | _, _, .cons_R (x1 := x1) (x2 := x2) hx hs => by
      simp only [List.filter_cons]
      rw [hP x1 x2 hx]
      split
      · exact .cons_R hx (list_R_filter hP hs)
      · exact list_R_filter hP hs

def list_R_append {A A' : Type} {rA : A → A' → Type} :
    ∀ {xs : List A} {xs' : List A'} {ys : List A} {ys' : List A'},
      list_R rA xs xs' → list_R rA ys ys' → list_R rA (xs ++ ys) (xs' ++ ys')
  | _, _, _, _, .nil_R, h => h
  | _, _, _, _, .cons_R hx hs, h => .cons_R hx (list_R_append hs h)

theorem nat_of_bin_zero : nat_of_bin (zero_op : N) = 0 := rfl
theorem nat_of_bin_one : nat_of_bin (one_op : N) = 1 := rfl
theorem nat_of_bin_add_op (a b : N) : nat_of_bin (add_op a b) = nat_of_bin a + nat_of_bin b :=
  nat_of_bin_add a b
theorem nat_of_bin_sub_op (a b : N) : nat_of_bin (sub_op a b) = nat_of_bin a - nat_of_bin b :=
  nat_of_bin_sub a b
theorem nat_of_bin_div_op (a b : N) : nat_of_bin (div_op a b) = nat_of_bin a / nat_of_bin b :=
  (nat_of_bin_div_mod a b).1
theorem nat_of_bin_mod_op (a b : N) : nat_of_bin (mod_op a b) = nat_of_bin a % nat_of_bin b :=
  (nat_of_bin_div_mod a b).2
theorem eq_op_N (a b : N) : eq_op a b = decide (nat_of_bin a = nat_of_bin b) := N_eqb_spec a b
theorem leq_op_N (a b : N) : leq_op a b = decide (nat_of_bin a ≤ nat_of_bin b) := N_leb_spec a b
theorem lt_op_N (a b : N) : lt_op a b = decide (nat_of_bin a < nat_of_bin b) := N_ltb_spec a b

/-! ### Auxiliary definitions -/

/-- A list of binary numbers as unary numbers. -/
def m_b2n (b : List N) : List Nat := b.map nat_of_bin

/-- A list of unary numbers as binary numbers. -/
def m_n2b (n : List Nat) : List N := n.map bin_of_nat

/-- Apply a function to both components of a pair. -/
def tmap {X Y : Type} (f : X → Y) (t : X × X) : Y × Y := (f t.1, f t.2)

/-- A pair of binary numbers as unary numbers. -/
def tb2tn (t : N × N) : Nat × Nat := tmap nat_of_bin t

/-- A pair of unary numbers as binary numbers. -/
def tn2tb (t : Nat × Nat) : N × N := tmap bin_of_nat t

/-- `tb2tn` on a list. -/
def m_tb2tn (xs : List (N × N)) : List (Nat × Nat) := xs.map tb2tn

/-- `tn2tb` on a list. -/
def m_tn2tb (xs : List (Nat × Nat)) : List (N × N) := xs.map tn2tb

/-! ### Basic arithmetic: generic definitions

The source's section declares all ten operation classes; as in Rocq, each definition takes only the operations
it uses. -/

/-- Generic predecessor. -/
def predn_T {T : Type} [one_of T] [sub_of T] (n : T) : T := sub_op n one_op

/-- Generic maximum. -/
def maxn_T {T : Type} [lt_of T] (m n : T) : T := if lt_op m n then n else m

/-- Generic minimum. -/
def minn_T {T : Type} [lt_of T] (m n : T) : T := if lt_op m n then m else n

/-- Generic "divides". -/
def dvdn_T {T : Type} [zero_of T] [mod_of T] [eq_of T] (d m : T) : Bool := eq_op (mod_op m d) zero_op

/-- Generic division with ceiling. -/
def div_ceil_T {T : Type} [zero_of T] [one_of T] [add_of T] [div_of T] [mod_of T] [eq_of T]
    (a b : T) : T :=
  if dvdn_T b a then div_op a b else add_op one_op (div_op a b)

/-! ### Basic arithmetic: refinements

The source's `Global Instance`s are `Type`-valued and are Lean definitions (`def`). -/

/-- Refinement of `nat_of_bin`. -/
def refine_b2n : refines (hrespectful (fun x y : N => PLift (unify x y)) Rnat) nat_of_bin id :=
  ⟨fun n n' h => Rnat_intro (by cases h.down; rfl)⟩

/-- Refinement of the predecessor. -/
def Rnat_pred : refines (hrespectful Rnat Rnat) Nat.pred predn_T :=
  ⟨fun a a' ha => Rnat_intro (by
    simp only [predn_T, nat_of_bin_sub_op, nat_of_bin_one, Rnat_eq ha, Nat.pred_eq_sub_one])⟩

/-- Refinement of "divides". -/
def refine_dvdn :
    refines (hrespectful Rnat (hrespectful Rnat bool_R)) (fun d m : Nat => decide (d ∣ m)) dvdn_T :=
  ⟨fun x x' rx y y' ry => bool_R_of_eq (by
    simp only [dvdn_T, eq_op_N, nat_of_bin_mod_op, nat_of_bin_zero, Rnat_eq rx, Rnat_eq ry]
    simp [Nat.dvd_iff_mod_eq_zero])⟩

/-- Refinement of the division with ceiling. -/
def refine_div_ceil :
    refines (hrespectful Rnat (hrespectful Rnat Rnat)) Prosa.Util.Div_mod.div_ceil div_ceil_T :=
  ⟨fun x x' rx y y' ry => Rnat_intro (by
    have hd : dvdn_T y' x' = decide (y ∣ x) := by
      simp only [dvdn_T, eq_op_N, nat_of_bin_mod_op, nat_of_bin_zero, Rnat_eq rx, Rnat_eq ry]
      simp [Nat.dvd_iff_mod_eq_zero]
    simp only [div_ceil_T, hd, Prosa.Util.Div_mod.div_ceil]
    by_cases h : y ∣ x
    · simp [h, nat_of_bin_div_op, Rnat_eq rx, Rnat_eq ry]
    · simp [h, nat_of_bin_add_op, nat_of_bin_one, nat_of_bin_div_op, Rnat_eq rx, Rnat_eq ry]; omega)⟩

/-- Refinement of the minimum. -/
def refine_minn : refines (hrespectful Rnat (hrespectful Rnat Rnat)) Nat.min minn_T :=
  ⟨fun a a' ra b b' rb => Rnat_intro (by
    simp only [minn_T, lt_op_N, Rnat_eq ra, Rnat_eq rb]
    by_cases h : a < b
    · simp [h, Rnat_eq ra]; omega
    · simp [h, Rnat_eq rb]; omega)⟩

/-- Refinement of the maximum. -/
def refine_maxn : refines (hrespectful Rnat (hrespectful Rnat Rnat)) Nat.max maxn_T :=
  ⟨fun a a' ra b b' rb => Rnat_intro (by
    simp only [maxn_T, lt_op_N, Rnat_eq ra, Rnat_eq rb]
    by_cases h : a < b
    · simp [h, Rnat_eq rb]; omega
    · simp [h, Rnat_eq ra]; omega)⟩

/-! ### Supporting lemmas -/

/-- A positive binary number is not `0`. -/
theorem posBinNatNotZero : ∀ p : positive, nat_of_bin (N.Npos p) ≠ 0 := by
  intro p h
  have := nat_of_pos_pos p
  simp only [nat_of_bin] at h
  omega

/-- If `b + 1` corresponds to the positive `p`, then `b` corresponds to the predecessor of `p`. -/
def eq_SnPos_to_nPred : ∀ (b : Nat) (p : positive), Rnat (b + 1) (N.Npos p) → Rnat b (Pos.pred_N p) :=
  fun b p h => Rnat_intro (by
    have := Rnat_eq h
    simp only [nat_of_bin] at this
    rw [nat_of_bin_pred_N, this]; rfl)

/-- Unary and binary `<` agree on related numbers. -/
def refine_ltn :
    ∀ (a : Nat) (a' : N) (b : Nat) (b' : N), Rnat a a' → Rnat b b' → bool_R (decide (a < b)) (lt_op a' b') :=
  fun a a' b b' ra rb => bool_R_of_eq (by rw [lt_op_N, Rnat_eq ra, Rnat_eq rb])

/-! ### Functions on lists: generic definitions -/

/-- Generic `iota`. -/
def iota_T {T : Type} [one_of T] [add_of T] : T → Nat → List T
  | _, 0 => []
  | a, b' + 1 => a :: iota_T (add_op a one_op) b'

/-- Generic `size`. -/
def size_T {T : Type} [zero_of T] [one_of T] [add_of T] {X : Type} : List X → T
  | [] => zero_op
  | _ :: s' => add_op one_op (size_T s')

/-- Generic forward shift. -/
def shift_points_pos_T {T : Type} [add_of T] (xs : List T) (s : T) : List T :=
  xs.map (fun x => add_op s x)

/-- Generic backward shift. -/
def shift_points_neg_T {T : Type} [sub_of T] [leq_of T] (xs : List T) (s : T) : List T :=
  let nonsmall := xs.filter (fun x => leq_op s x)
  nonsmall.map (fun x => sub_op x s)

/-! ### Functions on lists: refinements -/

/-- MathComp `last`: the last element of `x :: s`. -/
def seq_last {T : Type} : T → List T → T
  | x, [] => x
  | _, x' :: s' => seq_last x' s'

/-- Refinement of `map`. -/
def refine_map {A A' B B' : Type} (F : A → B) (F' : A' → B') (rA : A → A' → Type)
    (rB : B → B' → Type) (xs : List A) (xs' : List A') :
    refines (list_R rA) xs xs' → refines (hrespectful rA rB) F F' →
      refines (list_R rB) (xs.map F) (xs'.map F') :=
  fun Rxs RF => ⟨list_R_map RF.refines_rel Rxs.refines_rel⟩

/-- Refinement of `zip`. -/
def refine_zip :
    refines (hrespectful (list_R Rnat) (hrespectful (list_R Rnat) (list_R (prod_R Rnat Rnat))))
      List.zip List.zip :=
  ⟨fun _ _ Rxs => go Rxs⟩
where
  go : ∀ {xs : List Nat} {xs' : List N}, list_R Rnat xs xs' →
      ∀ (ys : List Nat) (ys' : List N), list_R Rnat ys ys' →
        list_R (prod_R Rnat Rnat) (List.zip xs ys) (List.zip xs' ys')
    | _, _, .nil_R, _, _, _ => .nil_R
    | _, _, .cons_R _ _, _, _, .nil_R => .nil_R
    | _, _, .cons_R hx hs, _, _, .cons_R hy hs' => .cons_R (.pair_R hx hy) (go hs _ _ hs')

/-- Refinement of `all`. -/
def refine_all {A A' : Type} (rA : A → A' → Type) :
    refines (hrespectful (hrespectful rA bool_R) (hrespectful (list_R rA) bool_R))
      (fun (P : A → Bool) (s : List A) => s.all P) (fun (P : A' → Bool) (s : List A') => s.all P) :=
  ⟨fun P P' RP xs xs' Rxs => bool_R_of_eq (go RP Rxs)⟩
where
  go {P : A → Bool} {P' : A' → Bool} (RP : hrespectful rA bool_R P P') :
      ∀ {xs : List A} {xs' : List A'}, list_R rA xs xs' → xs.all P = xs'.all P'
    | _, _, .nil_R => rfl
    | _, _, .cons_R (x1 := x1) (x2 := x2) hx hs => by
        simp only [List.all_cons, bool_R_eq (RP x1 x2 hx), go RP hs]

/-- Refinement of `flatten`. -/
def refine_flatten {A A' : Type} (rA : A → A' → Type) :
    refines (hrespectful (list_R (list_R rA)) (list_R rA)) List.flatten List.flatten :=
  ⟨fun _ _ Rxss => go Rxss⟩
where
  go : ∀ {xss : List (List A)} {xss' : List (List A')}, list_R (list_R rA) xss xss' →
      list_R rA xss.flatten xss'.flatten
    | _, _, .nil_R => .nil_R
    | _, _, .cons_R hx hs => list_R_append hx (go hs)

/-- Refinement of `cons`. -/
def refine_cons (A C : Type) (rAC : A → C → Type) :
    refines (hrespectful rAC (hrespectful (list_R rAC) (list_R rAC))) List.cons List.cons :=
  ⟨fun _ _ rh _ _ rt => .cons_R rh rt⟩

/-- Refinement of `nil`. -/
def refine_nil (A C : Type) (rAC : A → C → Type) : refines (list_R rAC) [] [] := ⟨.nil_R⟩

/-- Refinement of `last`. -/
def refine_last {A B : Type} (rA : A → B → Type) :
    refines (hrespectful rA (hrespectful (list_R rA) rA)) seq_last seq_last :=
  ⟨fun _ _ Rd _ _ Rxs => go Rd Rxs⟩
where
  go : ∀ {d : A} {d' : B}, rA d d' → ∀ {xs : List A} {xs' : List B}, list_R rA xs xs' →
      rA (seq_last d xs) (seq_last d' xs')
    | _, _, Rd, _, _, .nil_R => Rd
    | _, _, _, _, _, .cons_R hx hs => go hx hs

/-- Refinement of `size`. -/
def refine_size (A C : Type) (rAC : A → C → Type) :
    refines (hrespectful (list_R rAC) Rnat) List.length size_T :=
  ⟨fun _ _ Rs => Rnat_intro (go Rs)⟩
where
  go : ∀ {s : List A} {s' : List C}, list_R rAC s s' → nat_of_bin (size_T s' : N) = s.length
    | _, _, .nil_R => rfl
    | _, _, .cons_R _ hs => by
        simp only [size_T, nat_of_bin_add_op, nat_of_bin_one, go hs, List.length_cons]; omega

/-- `iota_T` on the successor of a predecessor. -/
theorem iotaTsuccN : ∀ (a : N) (p : positive),
    iota_T a (nat_of_bin (N.succ (Pos.pred_N p))) = a :: iota_T (succN a) (nat_of_bin (Pos.pred_N p)) := by
  intro a p
  rw [nat_of_bin_succ]
  simp only [iota_T, succN]
  congr 2
  apply nat_of_bin_inj
  simp only [nat_of_bin_add_op]; omega

/-- Refinement of `iota`. -/
def refine_iota :
    refines (hrespectful Rnat (hrespectful Rnat (list_R Rnat)))
      (fun a b : Nat => List.range' a b) (fun a b : N => iota_T a (nat_of_bin b)) :=
  ⟨fun a a' Ra b b' Rb => by rw [← Rnat_eq Rb]; exact go (nat_of_bin b') a a' Ra⟩
where
  go : ∀ (n : Nat) (a : Nat) (a' : N), Rnat a a' → list_R Rnat (List.range' a n) (iota_T a' n)
    | 0, _, _, _ => .nil_R
    | n + 1, a, a', Ra => .cons_R Ra (go n (a + 1) (add_op a' one_op)
        (Rnat_intro (by simp only [nat_of_bin_add_op, nat_of_bin_one, Rnat_eq Ra])))

/-- Refinement of `shift_points_pos`. -/
def refine_shift_points_pos :
    refines (hrespectful (list_R Rnat) (hrespectful Rnat (list_R Rnat)))
      Prosa.Util.List.shift_points_pos shift_points_pos_T :=
  ⟨fun _ _ Rxs _ _ Rs => list_R_map (fun x x' Rx => Rnat_intro (by
    simp only [nat_of_bin_add_op, Rnat_eq Rx, Rnat_eq Rs])) Rxs⟩

/-- Refinement of `shift_points_neg`. -/
def refine_shift_points_neg :
    refines (hrespectful (list_R Rnat) (hrespectful Rnat (list_R Rnat)))
      Prosa.Util.List.shift_points_neg shift_points_neg_T :=
  ⟨fun _ _ Rxs _ _ Rs => list_R_map (fun x x' Rx => Rnat_intro (by
      simp only [nat_of_bin_sub_op, Rnat_eq Rx, Rnat_eq Rs]))
    (list_R_filter (fun x x' Rx => by simp only [leq_op_N, Rnat_eq Rx, Rnat_eq Rs]) Rxs)⟩

/-- Binary numbers refine their unary interpretation. -/
def refine_abstract : ∀ xs : List N, refines (list_R Rnat) (xs.map nat_of_bin) xs :=
  fun xs => ⟨list_R_Rnat_of_eq xs⟩

/-! ### Supporting lemmas (lists) -/

/-- Refinement of `foldr`. -/
def refine_foldr_lemma :
    refines (hrespectful (hrespectful Rnat (hrespectful Rnat Rnat))
        (hrespectful Rnat (hrespectful (list_R Rnat) Rnat)))
      (@List.foldr Nat Nat) (@List.foldr N N) :=
  ⟨fun _ _ Rf _ _ Rd _ _ Rxs => go Rf Rd Rxs⟩
where
  go : ∀ {f : Nat → Nat → Nat} {f' : N → N → N}, hrespectful Rnat (hrespectful Rnat Rnat) f f' →
      ∀ {d : Nat} {d' : N}, Rnat d d' → ∀ {xs : List Nat} {xs' : List N}, list_R Rnat xs xs' →
        Rnat (xs.foldr f d) (xs'.foldr f' d')
    | _, _, _, _, _, Rd, _, _, .nil_R => Rd
    | _, _, Rf, _, _, Rd, _, _, .cons_R hx hs => Rf _ _ hx _ _ (go Rf Rd hs)

private theorem foldr_add_sum (xs : List Nat) : xs.foldr Nat.add 0 = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.foldr_cons, ih, Nat.add_eq]

private def foldr_add_Rnat : hrespectful Rnat (hrespectful Rnat Rnat) Nat.add (add_op : N → N → N) :=
  fun _ _ Ra _ _ Rb => Rnat_intro (by simp only [nat_of_bin_add_op, Rnat_eq Ra, Rnat_eq Rb]; rfl)

/-- Refinement of a conditional sum, computed by `foldr`. -/
def refine_foldr {T1 T2 : Type} (xs : List T1) (xs' : List T2) :
    ∀ (R : T1 → Bool) (R' : T2 → Bool) (F : T1 → Nat) (F' : T2 → N) (rT : T1 → T2 → Type),
      refines (list_R rT) xs xs' → refines (hrespectful rT Rnat) F F' → refines (hrespectful rT bool_R) R R' →
        refines Rnat (Prosa.Util.Sum.sumFiltered xs R F)
          (List.foldr add_op zero_op ((xs'.filter R').map F')) :=
  fun R R' F F' rT Rxs Rf Rr => ⟨by
    have h : Prosa.Util.Sum.sumFiltered xs R F = ((xs.filter R).map F).foldr Nat.add 0 := by
      simp only [Prosa.Util.Sum.sumFiltered, foldr_add_sum]
    rw [h]
    exact refine_foldr_lemma.go foldr_add_Rnat (Rnat_intro rfl)
      (list_R_map Rf.refines_rel
        (list_R_filter (fun x x' Rx => bool_R_eq (Rr.refines_rel x x' Rx)) Rxs.refines_rel))⟩

/-- Refinement of an unconditional sum, computed by `foldr`. -/
def refine_uncond_foldr {T1 T2 : Type} (xs : List T1) (xs' : List T2) :
    ∀ (F : T1 → Nat) (F' : T2 → N) (rT : T1 → T2 → Type),
      refines (list_R rT) xs xs' → refines (hrespectful rT Rnat) F F' →
        refines Rnat (Prosa.Util.Sum.sumSeq xs F) (List.foldr add_op zero_op (xs'.map F')) :=
  fun F F' rT Rxs Rf => ⟨by
    have h : Prosa.Util.Sum.sumSeq xs F = (xs.map F).foldr Nat.add 0 := by
      simp only [Prosa.Util.Sum.sumSeq, foldr_add_sum]
    rw [h]
    exact refine_foldr_lemma.go foldr_add_Rnat (Rnat_intro rfl) (list_R_map Rf.refines_rel Rxs.refines_rel)⟩

/-- Refinement of a conditional maximum, computed by `foldr`. -/
def refine_foldr_max {T1 T2 : Type} (xs : List T1) (xs' : List T2) :
    ∀ (R : T1 → Bool) (R' : T2 → Bool) (F : T1 → Nat) (F' : T2 → N) (rT : T1 → T2 → Type),
      refines (list_R rT) xs xs' → refines (hrespectful rT Rnat) F F' → refines (hrespectful rT bool_R) R R' →
        refines Rnat (Prosa.Util.Sum.maxFiltered xs R F)
          (List.foldr maxn_T zero_op ((xs'.filter R').map F')) :=
  fun R R' F F' rT Rxs Rf Rr => ⟨by
    simp only [Prosa.Util.Sum.maxFiltered]
    have hmax : hrespectful Rnat (hrespectful Rnat Rnat) max (maxn_T : N → N → N) := by
      intro a a' Ra b b' Rb
      have := (refine_maxn.refines_rel a a' Ra b b' Rb)
      exact Rnat_intro (Rnat_eq this)
    exact refine_foldr_lemma.go hmax (Rnat_intro rfl)
      (list_R_map Rf.refines_rel
        (list_R_filter (fun x x' Rx => bool_R_eq (Rr.refines_rel x x' Rx)) Rxs.refines_rel))⟩

end Prosa.Implementation.Refinements.Refinements
