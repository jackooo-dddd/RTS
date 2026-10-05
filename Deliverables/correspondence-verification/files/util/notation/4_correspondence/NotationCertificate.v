From FoundationImported Require Import ImportedNotation.
From prosa Require Import util.notation.

(** The actual source and imported definitions compute to the same constant
    function when their carrier types are identified. *)
Lemma constant_value_certificate
    (X Y : Type) (c : Y) (x : X) :
  Logic.eq
    (@prosa.util.notation.constant X Y c x)
    (@Prosa_Util_Notation_constant X Y c x).
Proof. reflexivity. Qed.

