From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduleChange.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ScheduleChangeBaseAdapter ScheduleChangeStateAdapter.

Definition sc_option_to_source {T : Type}
    (x : ImportedScheduleChange.Option T) : option T :=
  match x with
  | ImportedScheduleChange.Option_none => None
  | ImportedScheduleChange.Option_some j => Some j
  end.

Lemma sc_option_source_roundtrip {T : Type} (x : option T) :
  Logic.eq (sc_option_to_source (sc_option_to_imported x)) x.
Proof. destruct x; reflexivity. Qed.

Lemma sc_option_target_roundtrip {T : Type}
    (x : ImportedScheduleChange.Option T) :
  ScOptionRel (sc_option_to_source x) x.
Proof. destruct x; cbn; exact (@Lean.eq_refl _ _). Qed.

Lemma sc_option_eq_correspondence (T : Type)
    (aR bR : option T) (aL bL : ImportedScheduleChange.Option T) :
  ScOptionRel aR aL -> ScOptionRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (sc_option_to_imported aR)
        (sc_option_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal sc_option_to_source
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (sc_option_source_roundtrip aR) in Hdecoded.
    rewrite (sc_option_source_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Definition sc_target_false_elim (Q : SProp)
    (H : ImportedScheduleChange.False) : Q := match H return Q with end.

Lemma sc_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedScheduleChange.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  ScBoolRel bR (ImportedScheduleChange.Decidable_decide Q d).
Proof.
  intro Hrel. unfold ScBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (sc_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (sc_target_false_elim _ (sc_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma sc_option_ne_correspondence (T : eqType)
    (aR bR : option T) (aL bL : ImportedScheduleChange.Option T) :
  ScOptionRel aR aL -> ScOptionRel bR bL ->
  PropSPropRel (is_true (aR != bR))
    (ImportedScheduleChange.Ne (ImportedScheduleChange.Option T) aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intros Hneq HeqL.
    have HeqR := sprop_to_prop _ _
      (sc_option_eq_correspondence T aR bR aL bL Ha Hb) HeqL.
    subst bR. rewrite eqxx in Hneq. discriminate Hneq.
  - intro HneqL.
    destruct (@eqP _ aR bR) as [HeqR | HneqR].
    + exact (sc_target_false_elim _
        (HneqL (prop_to_sprop _ _
          (sc_option_eq_correspondence T aR bR aL bL Ha Hb) HeqR))).
    + apply strictly_inhabits. exact (Logic.eq_refl true).
Qed.
