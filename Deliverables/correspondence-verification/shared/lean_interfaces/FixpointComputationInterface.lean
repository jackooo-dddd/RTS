import Prosa.Util.Fixpoint

namespace Prosa.Validation.FixpointInterface

open Prosa.Util.Fixpoint

theorem natBeqZeroZero : Nat.beq 0 0 = true := rfl
theorem natBeqZeroSucc (n : Nat) : Nat.beq 0 (n + 1) = false := rfl
theorem natBeqSuccZero (n : Nat) : Nat.beq (n + 1) 0 = false := rfl
theorem natBeqSuccSucc (n m : Nat) :
    Nat.beq (n + 1) (m + 1) = Nat.beq n m := rfl

theorem natBleZero (n : Nat) : Nat.ble 0 n = true := rfl
theorem natBleSuccZero (n : Nat) : Nat.ble (n + 1) 0 = false := rfl
theorem natBleSuccSucc (n m : Nat) :
    Nat.ble (n + 1) (m + 1) = Nat.ble n m := rfl

theorem natEqBoolTruth (a b : Nat) :
    (a.beq b = true) ↔ a = b := by
  simp

theorem natLeBoolTruth (a b : Nat) :
    (a.ble b = true) ↔ a ≤ b := by
  simp

theorem natEqDecideAgrees (a b : Nat) :
    decide (a = b) = a.beq b := by
  cases h : a.beq b
  · have hne : a ≠ b := by
      intro heq
      have htrue := (natEqBoolTruth a b).mpr heq
      simp [h] at htrue
    simp [hne, h]
  · have heq := (natEqBoolTruth a b).mp h
    simp [heq, h]

theorem natLeDecideAgrees (a b : Nat) :
    decide (a ≤ b) = a.ble b := by
  cases h : a.ble b
  · have hnle : ¬a ≤ b := by
      intro hle
      have htrue := (natLeBoolTruth a b).mpr hle
      simp [h] at htrue
    simp [hnle, h]
  · have hle := (natLeBoolTruth a b).mp h
    simp [hle, h]

theorem findFixpointFromZero (f : Nat → Nat) (x h : Nat) :
    find_fixpoint_from f x h 0 = none := rfl

theorem findFixpointFromSucc (f : Nat → Nat) (x h fuel : Nat) :
    find_fixpoint_from f x h (fuel + 1) =
      if (f x).beq x then some x
      else if (f x).ble h then find_fixpoint_from f (f x) h fuel
      else none := rfl

theorem findFixpointFromSuccOriginalSemantics (f : Nat → Nat)
    (x h fuel : Nat) :
    find_fixpoint_from f x h (fuel + 1) =
      if decide (f x = x) then some x
      else if decide (f x ≤ h) then find_fixpoint_from f (f x) h fuel
      else none := by
  rw [findFixpointFromSucc, natEqDecideAgrees, natLeDecideAgrees]

theorem findFixpointProjection (f : Nat → Nat) (h : Nat) :
    find_fixpoint f h = find_fixpoint_from f 1 h h := rfl

theorem findMaxFixpointOfSeqProjection
    (f : Nat → Nat → Nat) (sp : List Nat) (h : Nat) :
    find_max_fixpoint_of_seq f sp h =
      let fixpoints := sp.map (fun s => find_fixpoint (f s) h)
      let max := Prosa.Util.Minmax.bigMaxListCond fixpoints Option.isSome
        (fun fp => fp.getD 0)
      if fixpoints.all Option.isSome then some max else none := rfl

theorem findMaxFixpointProjection
    (L : Nat) (P : Nat → Bool) (f : Nat → Nat → Nat) (h : Nat) :
    find_max_fixpoint L P f h =
      let sp := (_root_.List.range L).filter P
      if (_root_.List.range L).any P then
        find_max_fixpoint_of_seq f sp h else none := rfl

theorem listMapNil {A B : Type} (f : A → B) :
    ([] : List A).map f = [] := rfl
theorem listMapCons {A B : Type} (f : A → B) (x : A) (xs : List A) :
    (x :: xs).map f = f x :: xs.map f := rfl
theorem listAllNil {A : Type} (P : A → Bool) :
    ([] : List A).all P = true := rfl
theorem listAllCons {A : Type} (P : A → Bool) (x : A) (xs : List A) :
    (x :: xs).all P = (P x && xs.all P) := rfl
theorem bigMaxNil {A : Type} (P : A → Bool) (F : A → Nat) :
    Prosa.Util.Minmax.bigMaxListCond ([] : List A) P F = 0 := rfl
theorem bigMaxCons {A : Type} (P : A → Bool) (F : A → Nat)
    (x : A) (xs : List A) :
    Prosa.Util.Minmax.bigMaxListCond (x :: xs) P F =
      if P x then Nat.max (F x) (Prosa.Util.Minmax.bigMaxListCond xs P F)
      else Prosa.Util.Minmax.bigMaxListCond xs P F := rfl
theorem natMaxZeroLeft (n : Nat) : Nat.max 0 n = n := by simp
theorem natMaxZeroRight (n : Nat) : Nat.max n 0 = n := by simp
theorem natMaxSuccSucc (n m : Nat) :
    Nat.max (Nat.succ n) (Nat.succ m) = Nat.succ (Nat.max n m) := by
  simp [Nat.max_def]
  split <;> rfl
theorem optionIsSomeNone {A : Type} :
    Option.isSome (none : Option A) = false := rfl
theorem optionIsSomeSome {A : Type} (x : A) :
    Option.isSome (some x : Option A) = true := rfl
theorem optionGetDNone {A : Type} (d : A) :
    Option.getD (none : Option A) d = d := rfl
theorem optionGetDSome {A : Type} (x d : A) :
    Option.getD (some x : Option A) d = x := rfl
theorem listAnyNil {A : Type} (P : A → Bool) :
    ([] : List A).any P = false := rfl
theorem listAnyCons {A : Type} (P : A → Bool) (x : A) (xs : List A) :
    (x :: xs).any P = (P x || xs.any P) := rfl
theorem listFilterNil {A : Type} (P : A → Bool) :
    ([] : List A).filter P = [] := rfl
theorem listFilterCons {A : Type} (P : A → Bool) (x : A) (xs : List A) :
    (x :: xs).filter P = if P x then x :: xs.filter P else xs.filter P := by
  cases h : P x <;> simp [h]
theorem listRangeZero : (_root_.List.range 0 : List Nat) = [] := rfl
theorem listRangeSucc (n : Nat) :
    _root_.List.range (Nat.succ n) = _root_.List.range n ++ [n] :=
  _root_.List.range_succ
theorem listAppendNil {A : Type} (ys : List A) : ([] : List A) ++ ys = ys := rfl
theorem listAppendCons {A : Type} (x : A) (xs ys : List A) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

#check @Prosa.Util.Fixpoint.find_fixpoint_from
#check @Prosa.Util.Fixpoint.find_fixpoint
#check @Prosa.Util.Fixpoint.find_max_fixpoint_of_seq
#check @Prosa.Util.Fixpoint.find_max_fixpoint

#print axioms Prosa.Util.Fixpoint.ffpf_finds_fixpoint
#print axioms Prosa.Util.Fixpoint.ffp_finds_fixpoint
#print axioms Prosa.Util.Fixpoint.no_fixpoint_skipped
#print axioms Prosa.Util.Fixpoint.ffpf_finds_least_fixpoint
#print axioms Prosa.Util.Fixpoint.ffp_finds_least_fixpoint
#print axioms Prosa.Util.Fixpoint.ffpf_finds_positive_fixpoint
#print axioms Prosa.Util.Fixpoint.ffp_finds_positive_fixpoint
#print axioms Prosa.Util.Fixpoint.ffpf_finds_none
#print axioms Prosa.Util.Fixpoint.ffp_finds_none
#print axioms Prosa.Util.Fixpoint.fmfs_finds_fixpoint
#print axioms Prosa.Util.Fixpoint.fmfs_is_maximum
#print axioms Prosa.Util.Fixpoint.fmf_finds_fixpoint
#print axioms Prosa.Util.Fixpoint.fmf_is_maximum

end Prosa.Validation.FixpointInterface
