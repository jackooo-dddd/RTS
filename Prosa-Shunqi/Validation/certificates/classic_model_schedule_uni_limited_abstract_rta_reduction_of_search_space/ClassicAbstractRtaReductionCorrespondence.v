From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.epsilon classic.model.time classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicAbstractRtaReduction.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicAbstractRtaReductionBase ClassicAbstractRtaReductionList.

Module I := ImportedClassicAbstractRtaReduction.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/abstract_RTA/reduction_of_search_space.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the task type and the value type [T] are [eqType]s, identified, with the Lean [DecidableEq] instances given
    by the eqTypes' decision procedures ([ct_decidable_eq]); times by [SubNatRel]; functions [nat -> T] pointwise on
    related arguments (identical values), functions [nat -> nat] and interference bound functions
    [Task -> time -> time -> time] pointwise on related arguments and values; all with two-way totals.  At [T = nat]
    (the instance used by [is_in_search_space] and the statements) the value type is related by [SubNatRel] and the
    Lean instance is the core [Nat] decision.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

Lemma cl_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cl_nat_input nR nL : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof. intro H. rewrite (cl_nat_logic _ _ H). exact (sub_nat_rocq_roundtrip nR). Qed.

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma crs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma crs_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma crs_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) crs_false_rel). Qed.

Lemma crs_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)



(* ------------------------------------------------------------------ *)
(** * Relations *)

Lemma crs_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CrsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CrsNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CrsIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CrsNatFunRel (fR tsk aR) (fL tsk aL).

Definition crs_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition crs_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma crs_ibf_canonical (Task : Type) fR : CrsIbfRel Task fR (crs_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold crs_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma crs_ibf_surjective (Task : Type) fL : CrsIbfRel Task (crs_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma crs_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CrsIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (crs_forall_cover _ _ (CrsIbfRel Task) (crs_ibf_to_target Task) (crs_ibf_to_source Task) (crs_ibf_canonical Task) (crs_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem AbstractRTAReduction_are_equivalent_at_values_less_than_correspondence (T : eqType) f1R f1L (H1 : CrsFunRel T f1R f1L)
    f2R f2L (H2 : CrsFunRel T f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_equivalent_at_values_less_than T (ct_decidable_eq T) f1L f2L BL).
Proof.
  apply: ct_forall_nat => xR xL Hx.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (crs_eq_transport T _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)).
Qed.

Theorem AbstractRTAReduction_are_not_equivalent_at_values_less_than_correspondence (T : eqType) f1R f1L (H1 : CrsFunRel T f1R f1L)
    f2R f2L (H2 : CrsFunRel T f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than T (ct_decidable_eq T) f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (crs_eq_transport T _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) crs_false_rel).
Qed.

(** The [T = nat] instances used by [is_in_search_space] and the statements. *)
Lemma crs_equiv_nat f1R f1L (H1 : CrsNatFunRel f1R f1L) f2R f2L (H2 : CrsNatFunRel f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_equivalent_at_values_less_than_inst1 Lean.Nat I.instDecidableEqNat f1L f2L BL).
Proof.
  apply: ct_forall_nat => xR xL Hx.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (sub_nat_eq_correspondence _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)).
Qed.

Lemma crs_not_equiv_nat f1R f1L (H1 : CrsNatFunRel f1R f1L) f2R f2L (H2 : CrsNatFunRel f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than_inst1 Lean.Nat I.instDecidableEqNat f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (sub_nat_eq_correspondence _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) crs_false_rel).
Qed.

Theorem AbstractRTAReduction_is_in_search_space_correspondence (Task : eqType) tsk BR BL (HB : SubNatRel BR BL)
    fR fL (Hf : CrsIbfRel Task fR fL) AR AL (HA : SubNatRel AR AL) :
  PropSPropRel (AbstractRTAReduction.is_in_search_space tsk BR fR AR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_is_in_search_space Task (ct_decidable_eq Task) tsk BL fL AL).
Proof.
  apply: ct_or; first exact (sub_nat_eq_correspondence _ _ _ _ HA (sub_nat_rel_canonical 0)).
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) HA) (ct_decide_lt _ _ _ _ HA HB))).
  - exact (crs_not_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ HA (sub_nat_rel_canonical 1))) _ _ (Hf tsk _ _ HA) _ _ HB).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_representative_exists (Task : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTAReduction.representative_exists Task)).
Definition tgt_representative_exists (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_representative_exists Task (ct_decidable_eq Task))).

Theorem AbstractRTAReduction_representative_exists_correspondence (Task : eqType) :
  PropSPropRel (src_representative_exists Task) (tgt_representative_exists Task).
Proof.
  unfold src_representative_exists, tgt_representative_exists.
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => BR BL HB. apply: crs_forall_ibf => fR fL Hf.
  apply: ct_forall_nat => AR AL HA.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ HA HB).
  apply: ct_exists_nat => SR SL HS.
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ HS HA).
  apply: ct_and; first exact (crs_equiv_nat _ _ (Hf tsk _ _ HA) _ _ (Hf tsk _ _ HS) _ _ HB).
  exact (AbstractRTAReduction_is_in_search_space_correspondence Task tsk BR BL HB fR fL Hf SR SL HS).
Qed.

Definition src_solution_for_A_exists (Task : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTAReduction.solution_for_A_exists Task)).
Definition tgt_solution_for_A_exists (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_solution_for_A_exists Task (ct_decidable_eq Task))).

Theorem AbstractRTAReduction_solution_for_A_exists_correspondence (Task : eqType) :
  PropSPropRel (src_solution_for_A_exists Task) (tgt_solution_for_A_exists Task).
Proof.
  unfold src_solution_for_A_exists, tgt_solution_for_A_exists.
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => BR BL HB. apply: crs_forall_ibf => fR fL Hf.
  apply: ct_forall_nat => AsR AsL HAs. apply: ct_forall_nat => FsR FsL HFs.
  have HS := sub_add_correspondence _ _ _ _ HAs HFs.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ HS HB).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ HS (Hf tsk _ _ HAs _ _ HS)).
  apply: ct_forall_nat => AR AL HA.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HAs HA) (ct_decide_le _ _ _ _ HA HS))).
  apply: ct_imp; first exact (crs_equiv_nat _ _ (Hf tsk _ _ HA) _ _ (Hf tsk _ _ HAs) _ _ HB).
  apply: ct_exists_nat => FR FL HF.
  have HAF := sub_add_correspondence _ _ _ _ HA HF.
  apply: ct_and; first exact (sub_nat_eq_correspondence _ _ _ _ HS HAF).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ HF HFs).
  exact (sub_nat_eq_correspondence _ _ _ _ HAF (Hf tsk _ _ HA _ _ HAF)).
Qed.
