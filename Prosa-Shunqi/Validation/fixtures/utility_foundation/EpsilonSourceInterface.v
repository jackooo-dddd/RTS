Require Import prosa.util.epsilon.

Module EpsilonSourceInterface.

(** Observable validation interface for the official parsing notation. *)
Definition epsilon_nat_value : nat := ε.

Lemma epsilon_nat_value_eq_one : epsilon_nat_value = 1.
Proof. reflexivity. Qed.

End EpsilonSourceInterface.
