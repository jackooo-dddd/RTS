From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import prosa.analysis.abstract.search_space.

Definition ss_source_equivalent_type_guard (T : eqType)
    (f1 f2 : nat -> T) (B : nat)
    (H : @are_equivalent_at_values_less_than T f1 f2 B) :
  forall x : nat, is_true (ltn x B) -> Logic.eq (f1 x) (f2 x) := H.

Definition ss_source_not_equivalent_type_guard (T : eqType)
    (f1 f2 : nat -> T) (B : nat)
    (H : @are_not_equivalent_at_values_less_than T f1 f2 B) :
  exists x : nat, is_true (ltn x B) /\ f1 x <> f2 x := H.

Definition ss_source_search_space_type_guard (B : nat)
    (ibf : nat -> nat -> nat) (A : nat)
    (H : is_in_search_space B ibf A) :
  A = O \/
    is_true (andb (ltn O A) (ltn A B)) /\
    @are_not_equivalent_at_values_less_than _
      (ibf (subn A (S O))) (ibf A) B := H.

Definition ss_source_representative_type_guard (B : nat)
    (ibf : nat -> nat -> nat) (A : nat)
    (Hlt : is_true (ltn A B)) :
  exists asp : nat,
    is_true (leq asp A) /\
    @are_equivalent_at_values_less_than _ (ibf A) (ibf asp) B /\
    is_in_search_space B ibf asp :=
  representative_exists B ibf A Hlt.

Definition ss_source_solution_type_guard (B : nat)
    (ibf : nat -> nat -> nat) (asp fsp : nat)
    (Hless : is_true (ltn (addn asp fsp) B))
    (Hfix : is_true (leq (ibf asp (addn asp fsp)) (addn asp fsp)))
    (A : nat)
    (Hbounds : is_true (andb (leq asp A) (leq A (addn asp fsp))))
    (Hequiv : @are_equivalent_at_values_less_than _ (ibf A) (ibf asp) B) :
  exists f : nat,
    addn asp fsp = addn A f /\
    is_true (leq f fsp) /\
    is_true (leq (ibf A (addn A f)) (addn A f)) :=
  solution_for_A_exists B ibf asp fsp Hless Hfix A Hbounds Hequiv.

Definition ss_source_switch_type_guard (B : nat)
    (ibf1 ibf2 : nat -> nat -> nat)
    (Heq : forall A d : nat,
      is_true (ltn A B) -> ibf1 A d = ibf2 A d)
    (A : nat) (Hspace : is_in_search_space B ibf1 A) :
  is_in_search_space B ibf2 A :=
  search_space_switch_IBF B ibf1 ibf2 Heq A Hspace.

Set Printing Implicit.
Check are_equivalent_at_values_less_than.
Check are_not_equivalent_at_values_less_than.
Check is_in_search_space.
Check representative_exists.
Check solution_for_A_exists.
Check search_space_switch_IBF.

Print Assumptions representative_exists.
Print Assumptions solution_for_A_exists.
Print Assumptions search_space_switch_IBF.
