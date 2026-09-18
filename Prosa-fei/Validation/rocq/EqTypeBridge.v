From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ProcessorStateBridge.

(** Lean's translation represents a MathComp [eqType] carrier as a plain
    imported Lean [Type] plus [DecidableEq].  This supplies a canonical
    (classical but proof-independent) imported decision procedure on the same
    carrier. *)
Definition imported_classical_decidable_eq (T : Type) : DecidableEq T :=
  fun x y => Classical_propDecidable (eq x y).

Definition imported_eq_sym {T : Type} (x y : T) : eq x y -> eq y x :=
  fun H =>
    match H in eq _ z return eq z x with
    | eq_refl => eq_refl x
    end.

(** These two terms cross only equality/reflection singletons.  Writing the
    dependent matches explicitly avoids relevance bugs in tactic-generated
    proof terms when the codomain is [SProp]. *)
Definition eqtype_truth_to_imported_eq (T : eqType) (x y : T) :
    RocqBoolTruth (x == y) -> eq x y :=
  match @eqP T x y as r in reflect _ b return
    RocqBoolTruth b -> eq x y
  with
  | ReflectT Hxy => fun _ =>
      match Hxy as H in Logic.eq _ z return eq x z with
      | Logic.eq_refl => eq_refl x
      end
  | ReflectF _ => Validation_false_elim _
  end.

Definition coq_bool_true_to_rocq_truth (b : bool)
    (H : Logic.eq b true) : RocqBoolTruth b :=
  match Logic.eq_sym H in Logic.eq _ b0 return RocqBoolTruth b0 with
  | Logic.eq_refl => Validation_sI
  end.

Definition eqtype_refl_truth (T : eqType) (x : T) :
    RocqBoolTruth (x == x) :=
  coq_bool_true_to_rocq_truth (x == x) (eqxx x).

Definition imported_eq_to_eqtype_truth (T : eqType) (x y : T) :
    eq x y -> RocqBoolTruth (x == y) :=
  fun Hxy =>
    match Hxy in eq _ z return RocqBoolTruth (x == z) with
    | eq_refl => eqtype_refl_truth T x
    end.

Definition imported_option_some_congr {T : Type} (x y : T) :
    eq x y ->
    eq (Option_some_inst1 T x) (Option_some_inst1 T y) :=
  fun Hxy =>
    match Hxy in eq _ z return
      eq (Option_some_inst1 T x) (Option_some_inst1 T z)
    with
    | eq_refl => eq_refl (Option_some_inst1 T x)
    end.

Definition imported_option_some_inj {T : Type} (x y : T) :
    eq (Option_some_inst1 T x) (Option_some_inst1 T y) -> eq x y :=
  fun Hxy =>
    match Hxy in eq _ o return
      match o with
      | Option_none_inst1 => Validation_SFalse
      | Option_some_inst1 z => eq x z
      end
    with
    | eq_refl => eq_refl x
    end.

(** Observable equality preservation for the representation change
    [eqType] -> [Type + DecidableEq]. *)
Lemma eqtype_bool_eq_imported_decide (T : eqType) (x y : T) :
  ImportedBoolRel
    (x == y)
    (Decidable_decide
       (eq x y)
       (imported_classical_decidable_eq T x y)).
Proof.
  apply imported_decide_bridge.
  - exact (eqtype_truth_to_imported_eq T x y).
  - exact (imported_eq_to_eqtype_truth T x y).
Qed.

Lemma eqtype_option_some_imported_decide (T : eqType) (x y : T) :
  ImportedBoolRel
    (x == y)
    (Decidable_decide
       (eq (Option_some_inst1 T x) (Option_some_inst1 T y))
       (Option_instDecidableEq_inst1
          T (imported_classical_decidable_eq T)
          (Option_some_inst1 T x) (Option_some_inst1 T y))).
Proof.
  apply imported_decide_bridge.
  - intro Htruth.
    exact
      (imported_option_some_congr x y
         (eqtype_truth_to_imported_eq T x y Htruth)).
  - intro Hsome.
    exact
      (imported_eq_to_eqtype_truth T x y
         (imported_option_some_inj x y Hsome)).
Qed.
