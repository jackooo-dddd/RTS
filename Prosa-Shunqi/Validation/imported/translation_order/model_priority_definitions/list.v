From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.
Require Export mathcomp.zify.zify.
Require Import prosa.util.tactics.
Require Export prosa.util.supremum.

Module ListSemanticSource.

Definition max0 := foldl maxn 0.

Definition first0 := head 0.

Definition last0 := last 0.

Definition statement_last0_cons : Prop :=
  (forall (x : nat) (xs : seq nat), xs <> [::] -> last0 (x :: xs) = last0 xs).

Definition statement_last0_cat : Prop :=
  (forall xs_l xs_r : seq nat, xs_r <> [::] -> last0 (xs_l ++ xs_r) = last0 xs_r).

Definition statement_last0_nth : Prop :=
  (forall xs : seq nat, last0 xs = nth 0 xs (size xs).-1).

Definition statement_last0_ex_cat : Prop :=
  (forall (x : nat) (xs : seq nat), xs <> [::] -> last0 xs = x -> exists xsh : seq nat, xsh ++ [:: x] = xs).

Definition statement_last0_filter : Prop :=
  (forall (x : nat) (xs : seq nat) (P : nat -> bool), xs <> [::] -> last0 xs = x -> P x -> last0 [seq x0 <- xs | P x0] = x).

Definition statement_max0_cons : Prop :=
  (forall (x : nat) (xs : seq nat), max0 (x :: xs) = maxn x (max0 xs)).

Definition statement_max0_of_uniform_set : Prop :=
  (forall (k : Datatypes_nat__canonical__eqtype_Equality) (xs : seq Datatypes_nat__canonical__eqtype_Equality), 0 < size xs -> (forall x : Datatypes_nat__canonical__eqtype_Equality, x \in xs -> x = k) -> max0 xs = k).

Definition statement_in_max0_le : Prop :=
  (forall (xs : seq_predType Datatypes_nat__canonical__eqtype_Equality) (x : nat), x \in xs -> x <= max0 xs).

Definition statement_max0_in_seq : Prop :=
  (forall xs : seq nat, xs <> [::] -> max0 xs \in xs).

Definition statement_max0_2cons_eq : Prop :=
  (forall (x : nat) (xs : seq nat), max0 [:: x, x & xs] = max0 (x :: xs)).

Definition statement_max0_2cons_le : Prop :=
  (forall (x1 x2 : nat) (xs : seq nat), x1 <= x2 -> max0 [:: x1, x2 & xs] = max0 (x2 :: xs)).

Definition statement_max0_rem0 : Prop :=
  (forall xs : seq nat, max0 [seq x <- xs | 0 < x] = max0 xs).

Definition statement_last_of_seq_le_max_of_seq : Prop :=
  (forall xs : seq nat, last0 xs <= max0 xs).

Definition statement_max_of_dominating_seq : Prop :=
  (forall xs ys : seq nat, (forall n : nat, nth 0 xs n <= nth 0 ys n) -> max0 xs <= max0 ys).

Definition statement_rem_in : Prop :=
  (forall (X : eqType) (x y : X) (xs : seq X), x \in rem (T:=X) y xs -> x \in xs).

Definition statement_in_neq_impl_rem_in : Prop :=
  (forall (X : eqType) (x y : X) (xs : seq X), x \in xs -> x != y -> x \in rem (T:=X) y xs).

Definition statement_filter_size_rem : Prop :=
  (forall (X : eqType) (x : X) (xs : seq X) (P : pred X), x \in xs -> P x -> size [seq y <- xs | P y] = size [seq y <- rem (T:=X) x xs | P y] + 1).

Definition statement_in_seq_equiv_undup : Prop :=
  (forall (X : eqType) (xs : seq X) (x : X), (x \in undup xs) = (x \in xs)).

Definition statement_nth0_cons : Prop :=
  (forall (x : nat) (xs : seq nat) (n : nat), 0 < n -> nth 0 (x :: xs) n = nth 0 xs n.-1).

Definition statement_seq1_some : Prop :=
  (forall (T : eqType) (x y : T), ([:: x] == [:: y]) = (Some x == Some y)).

Definition statement_seq_elim_last : Prop :=
  (forall (X : Type) (n : nat) (xs : seq X), size xs = n.+1 -> exists (x : X) (xs__c : seq X), xs = xs__c ++ [:: x] /\ size xs__c = n).

Definition statement_in_cat : Prop :=
  (forall (X : eqType) (x : X) (xs : seq X), x \in xs -> exists xsl xsr : seq X, xs = xsl ++ [:: x] ++ xsr).

Definition statement_subseq_leq_size : Prop :=
  (forall (X : eqType) (xs ys : seq X), uniq xs -> (forall x : X, x \in xs -> x \in ys) -> size xs <= size ys).

Definition statement_in_zip : Prop :=
  (forall (X Y : eqType) (xs : seq X) (ys : seq Y) (x x__d : X) (y y__d : Y), size xs = size ys -> (exists idx : nat, idx < size xs /\ nth x__d xs idx = x /\ nth y__d ys idx = y) -> (x, y) \in zip xs ys).

Definition statement_filter_in_pred0 : Prop :=
  (forall (X : eqType) (xs : seq X) (P : pred X), (forall x : X, x \in xs -> ~~ P x) -> [seq x <- xs | P x] = [::]).

Definition statement_eq_ind_in_seq : Prop :=
  (forall (X : eqType) (a b : X) (xs : seq X), index a xs = index b xs -> a \in xs -> b \in xs -> a = b).

Definition statement_default_or_in : Prop :=
  (forall (X : eqType) (n : nat) (d : X) (xs : seq X), nth d xs n = d \/ nth d xs n \in xs).

Definition statement_exists_two : Prop :=
  (forall (X : eqType) (xs : seq X), 1 < size xs -> uniq xs -> exists a b : X, a <> b /\ a \in xs /\ b \in xs).

Definition statement_has_all_nilp : Prop :=
  (forall (T : eqType) (s : seq T) (P : pred T), all P s -> ~~ nilp s -> has P s).

Definition statement_sorted_split : Prop :=
  (forall (X : eqType) (xs : seq X) (P : X -> bool) (f : X -> nat) (t : nat), sorted (fun x y : X => f x <= f y) xs -> [seq x <- xs | P x] = [seq x <- xs | P x & f x <= t] ++ [seq x <- xs | P x & t < f x]).

Definition statement_sorted_cat : Prop :=
  (forall (X : eqType) (R : rel X) (xs1 xs2 : seq X), transitive (T:=X) R -> sorted R (xs1 ++ xs2) -> sorted R xs1 /\ sorted R xs2).

Definition statement_nonnil_last : Prop :=
  (forall (X : eqType) (xs : seq X) (d1 d2 : X), xs != [::] -> last d1 xs = last d2 xs).

Definition statement_filter_last_mem : Prop :=
  (forall (X : eqType) (xs : seq X) (d : X) (P : pred X), has P xs -> last d [seq x <- xs | P x] \in xs).

Fixpoint rem_all {X : eqType} (x : X) (xs : seq X) :=
  match xs with
  | [::] => [::]
  | a :: xs =>
    if a == x then rem_all x xs else a :: rem_all x xs
  end.

Definition statement_nin_rem_all : Prop :=
  (forall (X : eqType) (x : X) (xs : seq X), ~ x \in rem_all x xs).

Definition statement_in_rem_all : Prop :=
  (forall (X : eqType) (a x : X) (xs : seq X), a \in rem_all x xs -> a \in xs).

Definition statement_rem_lt_id : Prop :=
  (forall (x : nat) (xs : seq_predType Datatypes_nat__canonical__eqtype_Equality), (forall y : nat, y \in xs -> x < y) -> rem_all x xs = xs).

Definition range (a b : nat) := index_iota a b.+1.

Definition statement_iotaD_impl : Prop :=
  (forall n_le m n : nat, n_le <= n -> iota m n = iota m n_le ++ iota (m + n_le) (n - n_le)).

Definition statement_index_iota_lt_step : Prop :=
  (forall a b : nat, a < b -> index_iota a b = a :: index_iota a.+1 b).

Definition statement_index_iota_cat : Prop :=
  (forall t t1 t2 : nat, t1 <= t <= t2 -> index_iota t1 t2 = index_iota t1 t ++ index_iota t t2).

Definition statement_range_filter_2cons : Prop :=
  (forall (x : Datatypes_nat__canonical__eqtype_Equality) (xs : seq Datatypes_nat__canonical__eqtype_Equality) (k : nat), [seq ρ <- range 0 k | ρ \in [:: x, x & xs]] = [seq ρ <- range 0 k | ρ \in x :: xs]).

Definition statement_index_iota_filter_eqx : Prop :=
  (forall x a b : nat, a <= x < b -> [seq ρ <- index_iota a b | ρ == x] = [:: x]).

Definition statement_index_iota_filter_singl : Prop :=
  (forall x a b : nat, a <= x < b -> [seq ρ <- index_iota a b | ρ \in [:: x]] = [:: x]).

Definition statement_index_iota_filter_inxs : Prop :=
  (forall (a b x : nat) (xs : seq_predType Datatypes_nat__canonical__eqtype_Equality), x < a -> [seq ρ <- index_iota a b | ρ \in xs] = [seq ρ <- index_iota a b | ρ \in rem_all x xs]).

Definition statement_index_iota_filter_step : Prop :=
  (forall (x : nat) (xs : seq_predType Datatypes_nat__canonical__eqtype_Equality) (a b : nat), a <= x < b -> (forall y : nat, y \in xs -> x <= y) -> [seq ρ <- index_iota a b | ρ \in x :: xs] = x :: [seq ρ <- index_iota a b | ρ \in rem_all x xs]).

Definition statement_range_iota_filter_step : Prop :=
  (forall (x : nat) (xs : seq_predType Datatypes_nat__canonical__eqtype_Equality) (k : nat), x <= k -> (forall y : nat, y \in xs -> x <= y) -> [seq ρ <- range 0 k | ρ \in x :: xs] = x :: [seq ρ <- range 0 k | ρ \in rem_all x xs]).

Definition statement_iota_filter_gt : Prop :=
  (forall (x a b idx : nat) (P : nat -> bool), x < a -> idx < size [seq x0 <- index_iota a b | P x0] -> x < nth 0 [seq x0 <- index_iota a b | P x0] idx).

Definition statement_sub_count_seq : Prop :=
  (forall (X : eqType) (f g : pred X) (xs : seq X), {in xs, forall x : X, f x -> g x} -> count f xs <= count g xs).

Definition statement_count_predUI' : Prop :=
  (forall (P1 P2 : pred nat) (xs : seq nat), count (predU P1 P2) xs = count P1 xs + count P2 xs - count (predI P1 P2) xs).

Definition prefix_of {T : eqType} (xs ys : seq T) := exists xs_tail, xs ++ xs_tail = ys.

Definition strict_prefix_of {T : eqType} (xs ys : seq T) :=
  exists xs_tail, xs_tail <> [::] /\ xs ++ xs_tail = ys.

Definition shift_points_pos (xs : seq nat) (s : nat) : seq nat :=
  map (addn s) xs.

Definition shift_points_neg (xs : seq nat) (s : nat) : seq nat :=
  let nonsmall := filter (fun x => x >= s) xs in
  map (fun x => x - s) nonsmall.

End ListSemanticSource.
