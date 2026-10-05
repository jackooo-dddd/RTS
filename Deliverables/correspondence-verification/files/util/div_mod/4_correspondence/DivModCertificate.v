From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import GeneratedDivModSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedDivMod ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NatSubCorrespondence DivModCorrespondence
  SubadditivityClosureCertificate.

(** Actual imported target statements, specialized along the canonical
    [nat <-> Lean.Nat] representation map. *)

Definition dm_target_eqdivn_leqmodn : SProp :=
  forall t1 t2 h : nat,
    dm_imported_le (sub_nat_to_imported t1) (sub_nat_to_imported t2) ->
    Lean.eq
      (dm_imported_div (sub_nat_to_imported t1) (sub_nat_to_imported h))
      (dm_imported_div (sub_nat_to_imported t2) (sub_nat_to_imported h)) ->
    dm_imported_le
      (dm_imported_mod (sub_nat_to_imported t1) (sub_nat_to_imported h))
      (dm_imported_mod (sub_nat_to_imported t2) (sub_nat_to_imported h)).

Theorem eqdivn_leqmodn_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_eqdivn_leqmodn
    dm_target_eqdivn_leqmodn.
Proof.
  unfold GeneratedDivModSource.statement_eqdivn_leqmodn,
    dm_target_eqdivn_leqmodn.
  apply prop_sprop_rel_intro.
  - intros H t1 t2 h HleL HdivL.
    apply (prop_to_sprop _ _
      (dm_le_correspondence _ _ _ _
        (dm_mod_correspondence _ _ _ _
          (sub_nat_rel_canonical t1) (sub_nat_rel_canonical h))
        (dm_mod_correspondence _ _ _ _
          (sub_nat_rel_canonical t2) (sub_nat_rel_canonical h)))).
    apply H.
    + exact (sprop_to_prop _ _
        (dm_le_correspondence _ _ _ _
          (sub_nat_rel_canonical t1) (sub_nat_rel_canonical t2)) HleL).
    + exact (sprop_to_prop _ _
        (dm_eq_correspondence _ _ _ _
          (dm_div_correspondence _ _ _ _
            (sub_nat_rel_canonical t1) (sub_nat_rel_canonical h))
          (dm_div_correspondence _ _ _ _
            (sub_nat_rel_canonical t2) (sub_nat_rel_canonical h))) HdivL).
  - intro H. apply strictly_inhabits. intros t1 t2 h HleR HdivR.
    exact (sprop_to_prop _ _
      (dm_le_correspondence _ _ _ _
        (dm_mod_correspondence _ _ _ _
          (sub_nat_rel_canonical t1) (sub_nat_rel_canonical h))
        (dm_mod_correspondence _ _ _ _
          (sub_nat_rel_canonical t2) (sub_nat_rel_canonical h)))
      (H t1 t2 h
        (prop_to_sprop _ _
          (dm_le_correspondence _ _ _ _
            (sub_nat_rel_canonical t1) (sub_nat_rel_canonical t2)) HleR)
        (prop_to_sprop _ _
          (dm_eq_correspondence _ _ _ _
            (dm_div_correspondence _ _ _ _
              (sub_nat_rel_canonical t1) (sub_nat_rel_canonical h))
            (dm_div_correspondence _ _ _ _
              (sub_nat_rel_canonical t2) (sub_nat_rel_canonical h))) HdivR))).
Qed.

Definition dm_target_ltdivn_dvdn : SProp :=
  forall x y : nat,
    dm_imported_lt
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_div
        (dm_imported_add (sub_nat_to_imported x) dm_imported_one)
        (sub_nat_to_imported y)) ->
    dm_imported_dvd (sub_nat_to_imported y)
      (dm_imported_add (sub_nat_to_imported x) dm_imported_one).

Theorem ltdivn_dvdn_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_ltdivn_dvdn
    dm_target_ltdivn_dvdn.
Proof.
  unfold GeneratedDivModSource.statement_ltdivn_dvdn,
    dm_target_ltdivn_dvdn.
  apply prop_sprop_rel_intro.
  - intros H x y HltL.
    apply (prop_to_sprop _ _
      (dm_dvd_correspondence (x + 1)
        (dm_imported_add (sub_nat_to_imported x) dm_imported_one)
        y (sub_nat_to_imported y)
        (dm_add_correspondence _ _ _ _
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
        (sub_nat_rel_canonical y))).
    apply H. exact (sprop_to_prop _ _
      (dm_lt_correspondence _ _ _ _
        (dm_div_correspondence _ _ _ _
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical y))
        (dm_div_correspondence _ _ _ _
          (dm_add_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
          (sub_nat_rel_canonical y))) HltL).
  - intro H. apply strictly_inhabits. intros x y HltR.
    exact (sprop_to_prop _ _
      (dm_dvd_correspondence (x + 1)
        (dm_imported_add (sub_nat_to_imported x) dm_imported_one)
        y (sub_nat_to_imported y)
        (dm_add_correspondence _ _ _ _
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
        (sub_nat_rel_canonical y))
      (H x y (prop_to_sprop _ _
        (dm_lt_correspondence _ _ _ _
          (dm_div_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical y))
          (dm_div_correspondence _ _ _ _
            (dm_add_correspondence _ _ _ _
              (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
            (sub_nat_rel_canonical y))) HltR))).
Qed.

Definition dm_target_addn1_modn_commute : SProp :=
  forall x h : nat,
    dm_imported_lt dm_imported_zero (sub_nat_to_imported h) ->
    Lean.eq
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported h))
      (dm_imported_div
        (dm_imported_add (sub_nat_to_imported x) dm_imported_one)
        (sub_nat_to_imported h)) ->
    Lean.eq
      (dm_imported_mod
        (dm_imported_add (sub_nat_to_imported x) dm_imported_one)
        (sub_nat_to_imported h))
      (dm_imported_add
        (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported h))
        dm_imported_one).

Theorem addn1_modn_commute_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_addn1_modn_commute
    dm_target_addn1_modn_commute.
Proof.
  unfold GeneratedDivModSource.statement_addn1_modn_commute,
    dm_target_addn1_modn_commute.
  apply prop_sprop_rel_intro.
  - intros H x h HposL HdivL.
    apply (prop_to_sprop _ _
      (dm_eq_correspondence _ _ _ _
        (dm_mod_correspondence _ _ _ _
          (dm_add_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
          (sub_nat_rel_canonical h))
        (dm_add_correspondence _ _ _ _
          (dm_mod_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
          (sub_nat_rel_canonical 1)))).
    apply H.
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence O dm_imported_zero h
          (sub_nat_to_imported h) (sub_nat_rel_canonical O)
          (sub_nat_rel_canonical h)) HposL).
    + exact (sprop_to_prop _ _
        (dm_eq_correspondence _ _ _ _
          (dm_div_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
          (dm_div_correspondence _ _ _ _
            (dm_add_correspondence _ _ _ _
              (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
            (sub_nat_rel_canonical h))) HdivL).
  - intro H. apply strictly_inhabits. intros x h HposR HdivR.
    exact (sprop_to_prop _ _
      (dm_eq_correspondence _ _ _ _
        (dm_mod_correspondence _ _ _ _
          (dm_add_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
          (sub_nat_rel_canonical h))
        (dm_add_correspondence _ _ _ _
          (dm_mod_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
          (sub_nat_rel_canonical 1)))
      (H x h
        (prop_to_sprop _ _
          (dm_lt_correspondence O dm_imported_zero h
            (sub_nat_to_imported h) (sub_nat_rel_canonical O)
            (sub_nat_rel_canonical h)) HposR)
        (prop_to_sprop _ _
          (dm_eq_correspondence _ _ _ _
            (dm_div_correspondence _ _ _ _
              (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
            (dm_div_correspondence _ _ _ _
              (dm_add_correspondence _ _ _ _
                (sub_nat_rel_canonical x) (sub_nat_rel_canonical 1))
              (sub_nat_rel_canonical h))) HdivR))).
Qed.

Definition dm_target_addmod_le_mod : SProp :=
  forall x y h : nat,
    dm_imported_lt dm_imported_zero (sub_nat_to_imported h) ->
    Lean.eq
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported h))
      (dm_imported_div
        (dm_imported_add (sub_nat_to_imported x) (sub_nat_to_imported y))
        (sub_nat_to_imported h)) ->
    dm_imported_lt
      (dm_imported_add
        (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported h))
        (dm_imported_mod (sub_nat_to_imported y) (sub_nat_to_imported h)))
      (sub_nat_to_imported h).

Theorem addmod_le_mod_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_addmod_le_mod
    dm_target_addmod_le_mod.
Proof.
  unfold GeneratedDivModSource.statement_addmod_le_mod,
    dm_target_addmod_le_mod.
  apply prop_sprop_rel_intro.
  - intros H x y h HposL HdivL.
    apply (prop_to_sprop _ _
      (dm_lt_correspondence _ _ _ _
        (dm_add_correspondence _ _ _ _
          (dm_mod_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
          (dm_mod_correspondence _ _ _ _
            (sub_nat_rel_canonical y) (sub_nat_rel_canonical h)))
        (sub_nat_rel_canonical h))).
    apply H.
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence O dm_imported_zero h
          (sub_nat_to_imported h) (sub_nat_rel_canonical O)
          (sub_nat_rel_canonical h)) HposL).
    + exact (sprop_to_prop _ _
        (dm_eq_correspondence _ _ _ _
          (dm_div_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
          (dm_div_correspondence _ _ _ _
            (dm_add_correspondence _ _ _ _
              (sub_nat_rel_canonical x) (sub_nat_rel_canonical y))
            (sub_nat_rel_canonical h))) HdivL).
  - intro H. apply strictly_inhabits. intros x y h HposR HdivR.
    exact (sprop_to_prop _ _
      (dm_lt_correspondence _ _ _ _
        (dm_add_correspondence _ _ _ _
          (dm_mod_correspondence _ _ _ _
            (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
          (dm_mod_correspondence _ _ _ _
            (sub_nat_rel_canonical y) (sub_nat_rel_canonical h)))
        (sub_nat_rel_canonical h))
      (H x y h
        (prop_to_sprop _ _
          (dm_lt_correspondence O dm_imported_zero h
            (sub_nat_to_imported h) (sub_nat_rel_canonical O)
            (sub_nat_rel_canonical h)) HposR)
        (prop_to_sprop _ _
          (dm_eq_correspondence _ _ _ _
            (dm_div_correspondence _ _ _ _
              (sub_nat_rel_canonical x) (sub_nat_rel_canonical h))
            (dm_div_correspondence _ _ _ _
              (dm_add_correspondence _ _ _ _
                (sub_nat_rel_canonical x) (sub_nat_rel_canonical y))
              (sub_nat_rel_canonical h))) HdivR))).
Qed.

Definition dm_target_divn_leq : SProp :=
  forall k T x : nat,
    Lean.And
      (dm_imported_le
        (dm_imported_mul (sub_nat_to_imported k) (sub_nat_to_imported T))
        (sub_nat_to_imported x))
      (dm_imported_lt (sub_nat_to_imported x)
        (dm_imported_mul
          (dm_imported_add (sub_nat_to_imported k) dm_imported_one)
          (sub_nat_to_imported T))) ->
    Lean.eq
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported T))
      (sub_nat_to_imported k).

Theorem divn_leq_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_divn_leq
    dm_target_divn_leq.
Proof.
  unfold GeneratedDivModSource.statement_divn_leq, dm_target_divn_leq.
  apply prop_sprop_rel_intro.
  - intros H k T x [HleL HltL].
    apply (prop_to_sprop _ _
      (dm_eq_correspondence _ _ _ _
        (dm_div_correspondence _ _ _ _
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical T))
        (sub_nat_rel_canonical k))).
    apply H. apply/andP; split.
    + exact (sprop_to_prop _ _
        (dm_le_correspondence _ _ _ _
          (dm_mul_correspondence _ _ _ _
            (sub_nat_rel_canonical k) (sub_nat_rel_canonical T))
          (sub_nat_rel_canonical x)) HleL).
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence _ _ _ _
          (sub_nat_rel_canonical x)
          (dm_mul_correspondence _ _ _ _
            (dm_succ_correspondence k (sub_nat_to_imported k)
              (sub_nat_rel_canonical k))
            (sub_nat_rel_canonical T))) HltL).
  - intro H. apply strictly_inhabits. intros k T x HintervalR.
    move: HintervalR => /andP [HleR HltR].
    exact (sprop_to_prop _ _
      (dm_eq_correspondence _ _ _ _
        (dm_div_correspondence _ _ _ _
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical T))
        (sub_nat_rel_canonical k))
      (H k T x (Lean.And_intro _ _
        (prop_to_sprop _ _
          (dm_le_correspondence _ _ _ _
            (dm_mul_correspondence _ _ _ _
              (sub_nat_rel_canonical k) (sub_nat_rel_canonical T))
            (sub_nat_rel_canonical x)) HleR)
        (prop_to_sprop _ _
          (dm_lt_correspondence _ _ _ _
            (sub_nat_rel_canonical x)
            (dm_mul_correspondence _ _ _ _
              (dm_succ_correspondence k (sub_nat_to_imported k)
                (sub_nat_rel_canonical k))
              (sub_nat_rel_canonical T))) HltR)))).
Qed.

Theorem div_floor_definition_certificate xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (GeneratedDivModSource.div_floor xR yR)
    (dm_imported_div_floor xL yL).
Proof.
  unfold GeneratedDivModSource.div_floor.
  exact (dm_div_floor_correspondence xR xL yR yL).
Qed.

Theorem div_ceil_definition_certificate xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (GeneratedDivModSource.div_ceil xR yR)
    (dm_imported_div_ceil xL yL).
Proof.
  unfold GeneratedDivModSource.div_ceil.
  exact (dm_div_ceil_correspondence xR xL yR yL).
Qed.

(** Reusable source-local adapters.  These expose the two extracted,
    byte-identical computational definitions through the already certified
    arithmetic bridge. *)
Lemma dm_source_div_floor_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (GeneratedDivModSource.div_floor xR yR)
    (dm_imported_div_floor xL yL).
Proof. exact (div_floor_definition_certificate xR xL yR yL). Qed.

Lemma dm_source_div_ceil_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (GeneratedDivModSource.div_ceil xR yR)
    (dm_imported_div_ceil xL yL).
Proof. exact (div_ceil_definition_certificate xR xL yR yL). Qed.

Definition dm_target_div_ceil0 : SProp :=
  forall b : nat,
    Lean.eq
      (dm_imported_div_ceil dm_imported_zero (sub_nat_to_imported b))
      dm_imported_zero.

Theorem div_ceil0_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_div_ceil0
    dm_target_div_ceil0.
Proof.
  unfold GeneratedDivModSource.statement_div_ceil0, dm_target_div_ceil0.
  apply prop_sprop_rel_intro.
  - intros H b. apply (prop_to_sprop _ _
      (dm_eq_correspondence _ _ O dm_imported_zero
        (dm_source_div_ceil_correspondence O dm_imported_zero
          b (sub_nat_to_imported b)
          (sub_nat_rel_canonical O) (sub_nat_rel_canonical b))
        (sub_nat_rel_canonical O))).
    exact (H b).
  - intro H. apply strictly_inhabits. intro b.
    exact (sprop_to_prop _ _
      (dm_eq_correspondence _ _ O dm_imported_zero
        (dm_source_div_ceil_correspondence O dm_imported_zero
          b (sub_nat_to_imported b)
          (sub_nat_rel_canonical O) (sub_nat_rel_canonical b))
        (sub_nat_rel_canonical O)) (H b)).
Qed.

Definition dm_target_div_ceil_gt0 : SProp :=
  forall a b : nat,
    dm_imported_lt dm_imported_zero (sub_nat_to_imported a) ->
    dm_imported_lt dm_imported_zero (sub_nat_to_imported b) ->
    dm_imported_lt dm_imported_zero
      (dm_imported_div_ceil (sub_nat_to_imported a)
        (sub_nat_to_imported b)).

Theorem div_ceil_gt0_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_div_ceil_gt0
    dm_target_div_ceil_gt0.
Proof.
  unfold GeneratedDivModSource.statement_div_ceil_gt0,
    dm_target_div_ceil_gt0.
  apply prop_sprop_rel_intro.
  - intros H a b HaL HbL. apply (prop_to_sprop _ _
      (dm_lt_correspondence O dm_imported_zero
        (GeneratedDivModSource.div_ceil a b)
        (dm_imported_div_ceil (sub_nat_to_imported a)
          (sub_nat_to_imported b))
        (sub_nat_rel_canonical O)
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical b)))).
    apply H.
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence O dm_imported_zero a
          (sub_nat_to_imported a)
          (sub_nat_rel_canonical O) (sub_nat_rel_canonical a)) HaL).
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence O dm_imported_zero b
          (sub_nat_to_imported b)
          (sub_nat_rel_canonical O) (sub_nat_rel_canonical b)) HbL).
  - intro H. apply strictly_inhabits. intros a b HaR HbR.
    exact (sprop_to_prop _ _
      (dm_lt_correspondence O dm_imported_zero
        (GeneratedDivModSource.div_ceil a b)
        (dm_imported_div_ceil (sub_nat_to_imported a)
          (sub_nat_to_imported b))
        (sub_nat_rel_canonical O)
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical b)))
      (H a b
        (prop_to_sprop _ _
          (dm_lt_correspondence O dm_imported_zero a
            (sub_nat_to_imported a)
            (sub_nat_rel_canonical O) (sub_nat_rel_canonical a)) HaR)
        (prop_to_sprop _ _
          (dm_lt_correspondence O dm_imported_zero b
            (sub_nat_to_imported b)
            (sub_nat_rel_canonical O) (sub_nat_rel_canonical b)) HbR))).
Qed.

Definition dm_target_div_ceil_monotone1 : SProp :=
  forall d m n : nat,
    dm_imported_le (sub_nat_to_imported m) (sub_nat_to_imported n) ->
    dm_imported_le
      (dm_imported_div_ceil (sub_nat_to_imported m)
        (sub_nat_to_imported d))
      (dm_imported_div_ceil (sub_nat_to_imported n)
        (sub_nat_to_imported d)).

Theorem div_ceil_monotone1_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_div_ceil_monotone1
    dm_target_div_ceil_monotone1.
Proof.
  unfold GeneratedDivModSource.statement_div_ceil_monotone1,
    dm_target_div_ceil_monotone1.
  apply prop_sprop_rel_intro.
  - intros H d m n HleL. apply (prop_to_sprop _ _
      (dm_le_correspondence _ _ _ _
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical d))
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical n) (sub_nat_rel_canonical d)))).
    apply H. exact (sprop_to_prop _ _
      (dm_le_correspondence _ _ _ _
        (sub_nat_rel_canonical m) (sub_nat_rel_canonical n)) HleL).
  - intro H. apply strictly_inhabits. intros d m n HleR.
    exact (sprop_to_prop _ _
      (dm_le_correspondence _ _ _ _
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical d))
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical n) (sub_nat_rel_canonical d)))
      (H d m n (prop_to_sprop _ _
        (dm_le_correspondence _ _ _ _
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical n)) HleR))).
Qed.

Definition dm_target_leq_div_ceil_add1 : SProp :=
  forall delta T : nat,
    dm_imported_lt dm_imported_zero (sub_nat_to_imported T) ->
    dm_imported_le (sub_nat_to_imported T) (sub_nat_to_imported delta) ->
    dm_imported_lt
      (dm_imported_div_ceil
        (dm_imported_sub (sub_nat_to_imported delta)
          (sub_nat_to_imported T))
        (sub_nat_to_imported T))
      (dm_imported_div_ceil (sub_nat_to_imported delta)
        (sub_nat_to_imported T)).

Theorem leq_div_ceil_add1_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_leq_div_ceil_add1
    dm_target_leq_div_ceil_add1.
Proof.
  unfold GeneratedDivModSource.statement_leq_div_ceil_add1,
    dm_target_leq_div_ceil_add1.
  apply prop_sprop_rel_intro.
  - intros H delta T HposL HleL. apply (prop_to_sprop _ _
      (dm_lt_correspondence _ _ _ _
        (dm_source_div_ceil_correspondence _ _ _ _
          (dm_sub_correspondence _ _ _ _
            (sub_nat_rel_canonical delta) (sub_nat_rel_canonical T))
          (sub_nat_rel_canonical T))
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical delta) (sub_nat_rel_canonical T)))).
    apply H.
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence O dm_imported_zero T
          (sub_nat_to_imported T)
          (sub_nat_rel_canonical O) (sub_nat_rel_canonical T)) HposL).
    + exact (sprop_to_prop _ _
        (dm_le_correspondence T (sub_nat_to_imported T)
          delta (sub_nat_to_imported delta)
          (sub_nat_rel_canonical T) (sub_nat_rel_canonical delta)) HleL).
  - intro H. apply strictly_inhabits. intros delta T HposR HleR.
    exact (sprop_to_prop _ _
      (dm_lt_correspondence _ _ _ _
        (dm_source_div_ceil_correspondence _ _ _ _
          (dm_sub_correspondence _ _ _ _
            (sub_nat_rel_canonical delta) (sub_nat_rel_canonical T))
          (sub_nat_rel_canonical T))
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical delta) (sub_nat_rel_canonical T)))
      (H delta T
        (prop_to_sprop _ _
          (dm_lt_correspondence O dm_imported_zero T
            (sub_nat_to_imported T)
            (sub_nat_rel_canonical O) (sub_nat_rel_canonical T)) HposR)
        (prop_to_sprop _ _
          (dm_le_correspondence T (sub_nat_to_imported T)
            delta (sub_nat_to_imported delta)
            (sub_nat_rel_canonical T) (sub_nat_rel_canonical delta)) HleR))).
Qed.

Lemma dm_actual_subadditive_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel (prosa.util.subadditivity.subadditive fR)
    (ImportedDivMod.Prosa_Util_Subadditivity_subadditive fL).
Proof.
  intro Hf.
  change (PropSPropRel (prosa.util.subadditivity.subadditive fR)
    (ImportedSubadditivity.Prosa_Util_Subadditivity_subadditive fL)).
  exact (subadditive_correspondence_certificate fR fL Hf).
Qed.

Definition dm_target_div_ceil_subadditive : SProp :=
  forall T : nat,
    ImportedDivMod.Prosa_Util_Subadditivity_subadditive
      (fun x => dm_imported_div_ceil x (sub_nat_to_imported T)).

Definition dm_source_div_ceil_fixed_fun_rel (T : nat) :
  SubNatFunRel
    (fun x => GeneratedDivModSource.div_ceil x T)
    (fun x => dm_imported_div_ceil x (sub_nat_to_imported T)) :=
  fun xR xL Hx => dm_source_div_ceil_correspondence _ _ _ _
    Hx (sub_nat_rel_canonical T).

Theorem div_ceil_subadditive_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_div_ceil_subadditive
    dm_target_div_ceil_subadditive.
Proof.
  unfold GeneratedDivModSource.statement_div_ceil_subadditive,
    dm_target_div_ceil_subadditive.
  apply prop_sprop_rel_intro.
  - intros H T. exact (prop_to_sprop _ _
      (dm_actual_subadditive_correspondence _ _
        (dm_source_div_ceil_fixed_fun_rel T)) (H T)).
  - intro H. apply strictly_inhabits. intro T.
    exact (sprop_to_prop _ _
      (dm_actual_subadditive_correspondence _ _
        (dm_source_div_ceil_fixed_fun_rel T)) (H T)).
Qed.

Definition dm_target_div_ceil_multiple : SProp :=
  forall delta T n : nat,
    dm_imported_lt dm_imported_zero (sub_nat_to_imported T) ->
    dm_imported_lt
      (dm_imported_mul (sub_nat_to_imported T) (sub_nat_to_imported n))
      (sub_nat_to_imported delta) ->
    dm_imported_lt (sub_nat_to_imported n)
      (dm_imported_div_ceil (sub_nat_to_imported delta)
        (sub_nat_to_imported T)).

Theorem div_ceil_multiple_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_div_ceil_multiple
    dm_target_div_ceil_multiple.
Proof.
  unfold GeneratedDivModSource.statement_div_ceil_multiple,
    dm_target_div_ceil_multiple.
  apply prop_sprop_rel_intro.
  - intros H delta T n HposL HmulL. apply (prop_to_sprop _ _
      (dm_lt_correspondence _ _ _ _
        (sub_nat_rel_canonical n)
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical delta) (sub_nat_rel_canonical T)))).
    apply H.
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence O dm_imported_zero T
          (sub_nat_to_imported T)
          (sub_nat_rel_canonical O) (sub_nat_rel_canonical T)) HposL).
    + exact (sprop_to_prop _ _
        (dm_lt_correspondence _ _ _ _
          (dm_mul_correspondence _ _ _ _
            (sub_nat_rel_canonical T) (sub_nat_rel_canonical n))
          (sub_nat_rel_canonical delta)) HmulL).
  - intro H. apply strictly_inhabits. intros delta T n HposR HmulR.
    exact (sprop_to_prop _ _
      (dm_lt_correspondence _ _ _ _
        (sub_nat_rel_canonical n)
        (dm_source_div_ceil_correspondence _ _ _ _
          (sub_nat_rel_canonical delta) (sub_nat_rel_canonical T)))
      (H delta T n
        (prop_to_sprop _ _
          (dm_lt_correspondence O dm_imported_zero T
            (sub_nat_to_imported T)
            (sub_nat_rel_canonical O) (sub_nat_rel_canonical T)) HposR)
        (prop_to_sprop _ _
          (dm_lt_correspondence _ _ _ _
            (dm_mul_correspondence _ _ _ _
              (sub_nat_rel_canonical T) (sub_nat_rel_canonical n))
            (sub_nat_rel_canonical delta)) HmulR))).
Qed.

Definition dm_target_div_floor_add_g : SProp :=
  forall a b : nat,
    dm_imported_lt dm_imported_zero (sub_nat_to_imported b) ->
    dm_imported_lt (sub_nat_to_imported a)
      (dm_imported_add
        (dm_imported_mul
          (dm_imported_div_floor (sub_nat_to_imported a)
            (sub_nat_to_imported b))
          (sub_nat_to_imported b))
        (sub_nat_to_imported b)).

Theorem div_floor_add_g_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_div_floor_add_g
    dm_target_div_floor_add_g.
Proof.
  unfold GeneratedDivModSource.statement_div_floor_add_g,
    dm_target_div_floor_add_g.
  apply prop_sprop_rel_intro.
  - intros H a b HposL. apply (prop_to_sprop _ _
      (dm_lt_correspondence _ _ _ _
        (sub_nat_rel_canonical a)
        (dm_add_correspondence _ _ _ _
          (dm_mul_correspondence _ _ _ _
            (dm_source_div_floor_correspondence _ _ _ _
              (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
            (sub_nat_rel_canonical b))
          (sub_nat_rel_canonical b)))).
    apply H. exact (sprop_to_prop _ _
      (dm_lt_correspondence O dm_imported_zero b
        (sub_nat_to_imported b)
        (sub_nat_rel_canonical O) (sub_nat_rel_canonical b)) HposL).
  - intro H. apply strictly_inhabits. intros a b HposR.
    exact (sprop_to_prop _ _
      (dm_lt_correspondence _ _ _ _
        (sub_nat_rel_canonical a)
        (dm_add_correspondence _ _ _ _
          (dm_mul_correspondence _ _ _ _
            (dm_source_div_floor_correspondence _ _ _ _
              (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
            (sub_nat_rel_canonical b))
          (sub_nat_rel_canonical b)))
      (H a b (prop_to_sprop _ _
        (dm_lt_correspondence O dm_imported_zero b
          (sub_nat_to_imported b)
          (sub_nat_rel_canonical O) (sub_nat_rel_canonical b)) HposR))).
Qed.

Definition dm_target_mod_elim : SProp :=
  forall a b c : nat,
    dm_imported_lt (sub_nat_to_imported b) (sub_nat_to_imported c) ->
    Lean.eq
      (dm_imported_mod
        (dm_imported_sub
          (dm_imported_add (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported b))
        (sub_nat_to_imported c))
      (ImportedDivMod.ite Lean.Nat
        (dm_imported_le (sub_nat_to_imported b)
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
        (ImportedDivMod.Nat_decLe (sub_nat_to_imported b)
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
        (dm_imported_sub
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported b))
        (dm_imported_sub
          (dm_imported_add
            (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
            (sub_nat_to_imported c))
          (sub_nat_to_imported b))).

Theorem mod_elim_statement_certificate :
  PropSPropRel GeneratedDivModSource.statement_mod_elim dm_target_mod_elim.
Proof.
  unfold GeneratedDivModSource.statement_mod_elim, dm_target_mod_elim.
  apply prop_sprop_rel_intro.
  - intros H a b c HltL. apply (prop_to_sprop _ _
      (dm_eq_correspondence _ _ _ _
        (dm_mod_correspondence _ _ _ _
          (dm_sub_correspondence _ _ _ _
            (dm_add_correspondence _ _ _ _
              (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
            (sub_nat_rel_canonical b))
          (sub_nat_rel_canonical c))
        (sub_imported_eq_sym _ _ (dm_mod_elim_rhs_canonical a b c)))).
    apply H. exact (sprop_to_prop _ _
      (dm_lt_correspondence b (sub_nat_to_imported b)
        c (sub_nat_to_imported c)
        (sub_nat_rel_canonical b) (sub_nat_rel_canonical c)) HltL).
  - intro H. apply strictly_inhabits. intros a b c HltR.
    exact (sprop_to_prop _ _
      (dm_eq_correspondence _ _ _ _
        (dm_mod_correspondence _ _ _ _
          (dm_sub_correspondence _ _ _ _
            (dm_add_correspondence _ _ _ _
              (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
            (sub_nat_rel_canonical b))
          (sub_nat_rel_canonical c))
        (sub_imported_eq_sym _ _ (dm_mod_elim_rhs_canonical a b c)))
      (H a b c (prop_to_sprop _ _
        (dm_lt_correspondence b (sub_nat_to_imported b)
          c (sub_nat_to_imported c)
          (sub_nat_rel_canonical b) (sub_nat_rel_canonical c)) HltR))).
Qed.

Print Assumptions eqdivn_leqmodn_statement_certificate.
Print Assumptions ltdivn_dvdn_statement_certificate.
Print Assumptions addn1_modn_commute_statement_certificate.
Print Assumptions addmod_le_mod_statement_certificate.
Print Assumptions divn_leq_statement_certificate.
Print Assumptions div_floor_definition_certificate.
Print Assumptions div_ceil_definition_certificate.
Print Assumptions div_ceil0_statement_certificate.
Print Assumptions div_ceil_gt0_statement_certificate.
Print Assumptions div_ceil_monotone1_statement_certificate.
Print Assumptions leq_div_ceil_add1_statement_certificate.
Print Assumptions div_ceil_subadditive_statement_certificate.
Print Assumptions div_ceil_multiple_statement_certificate.
Print Assumptions div_floor_add_g_statement_certificate.
Print Assumptions mod_elim_statement_certificate.
