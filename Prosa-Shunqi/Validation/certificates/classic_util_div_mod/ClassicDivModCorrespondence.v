From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div.
From prosa Require Import classic.util.div_mod.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicDivMod.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicDivModNatSub ClassicDivModOps ClassicDivModBase.

Module I := ImportedClassicDivMod.
Local Open Scope nat_scope.

(** Certificates for [classic/util/div_mod.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: natural numbers by the accepted [SubNatRel] (two-way totals).
    Arithmetic: the accepted v0.6 operation-level bridge for [+], [*], [-],
    [%/], [%%], [<=], [<], [=] and [div_floor]/[div_ceil] ([DivModCorrespondence],
    re-bound as [ClassicDivModOps]); [div_floor]/[div_ceil] are the classic
    production definitions, bound by the same-named exported interface
    equations.  Statements: the source side is the exact elaborated type of the
    pinned lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma cd_iff (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [f g]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (f (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (g (sprop_to_prop _ _ HQ q))).
  - intros [f g]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (f (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (g (prop_to_sprop _ _ HQ q))).
Qed.

Notation c0 := (sub_nat_rel_canonical 0).
Notation c1 := (sub_nat_rel_canonical 1).
Notation cle := dm_le_correspondence.
Notation clt := dm_lt_correspondence.
Notation ceq := dm_eq_correspondence.
Notation cadd := dm_add_correspondence.
Notation cmul := dm_mul_correspondence.
Notation csub := dm_sub_correspondence.
Notation cdiv := dm_div_correspondence.
Notation cmod := dm_mod_correspondence.
Notation csucc := dm_succ_correspondence.

Lemma cd_ceil xR xL yR yL : SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (div_mod.div_ceil xR yR) (I.Prosa_Classic_Util_DivMod_div_ceil xL yL).
Proof. exact (dm_div_ceil_correspondence xR xL yR yL). Qed.

Theorem div_floor_correspondence xR xL yR yL : SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (div_mod.div_floor xR yR) (I.Prosa_Classic_Util_DivMod_div_floor xL yL).
Proof. exact (dm_div_floor_correspondence xR xL yR yL). Qed.

Theorem div_ceil_correspondence xR xL yR yL : SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (div_mod.div_ceil xR yR) (I.Prosa_Classic_Util_DivMod_div_ceil xL yL).
Proof. exact (cd_ceil xR xL yR yL). Qed.

Definition src_ltn_div_trunc : Prop := ltac:(type_of_term @ltn_div_trunc).
Definition tgt_ltn_div_trunc : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_ltn_div_trunc).
Theorem ltn_div_trunc_correspondence : PropSPropRel src_ltn_div_trunc tgt_ltn_div_trunc.
Proof.
  unfold src_ltn_div_trunc, tgt_ltn_div_trunc.
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => d dL Hd.
  apply: ct_imp; first exact (clt _ _ _ _ c0 Hd).
  exact (ct_imp _ _ _ _ (clt _ _ _ _ (cdiv _ _ _ _ Hm Hd) (cdiv _ _ _ _ Hn Hd)) (clt _ _ _ _ Hm Hn)).
Qed.

Definition src_subndiv_eq_mod : Prop := ltac:(type_of_term @subndiv_eq_mod).
Definition tgt_subndiv_eq_mod : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_subndiv_eq_mod).
Theorem subndiv_eq_mod_correspondence : PropSPropRel src_subndiv_eq_mod tgt_subndiv_eq_mod.
Proof.
  unfold src_subndiv_eq_mod, tgt_subndiv_eq_mod.
  apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => d dL Hd.
  exact (ceq _ _ _ _ (csub _ _ _ _ Hn (cmul _ _ _ _ (cdiv _ _ _ _ Hn Hd) Hd)) (cmod _ _ _ _ Hn Hd)).
Qed.

Definition src_divSn_cases : Prop := ltac:(type_of_term @divSn_cases).
Definition tgt_divSn_cases : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_divSn_cases).
Theorem divSn_cases_correspondence : PropSPropRel src_divSn_cases tgt_divSn_cases.
Proof.
  unfold src_divSn_cases, tgt_divSn_cases.
  apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => d dL Hd. have Hs := csucc _ _ Hn.
  apply: ct_imp; first exact (clt _ _ _ _ c1 Hd).
  apply: ct_or.
  - exact (ct_and _ _ _ _ (ceq _ _ _ _ (cdiv _ _ _ _ Hn Hd) (cdiv _ _ _ _ Hs Hd))
            (ceq _ _ _ _ (cadd _ _ _ _ (cmod _ _ _ _ Hn Hd) c1) (cmod _ _ _ _ Hs Hd))).
  - exact (ceq _ _ _ _ (cadd _ _ _ _ (cdiv _ _ _ _ Hn Hd) c1) (cdiv _ _ _ _ Hs Hd)).
Qed.

Definition src_ceil_neq0 : Prop := ltac:(type_of_term @ceil_neq0).
Definition tgt_ceil_neq0 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_ceil_neq0).
Theorem ceil_neq0_correspondence : PropSPropRel src_ceil_neq0 tgt_ceil_neq0.
Proof.
  unfold src_ceil_neq0, tgt_ceil_neq0.
  apply: ct_forall_nat => x xL Hx. apply: ct_forall_nat => y yL Hy.
  apply: ct_imp; first exact (clt _ _ _ _ c0 Hx).
  exact (ct_imp _ _ _ _ (clt _ _ _ _ c0 Hy) (clt _ _ _ _ c0 (cd_ceil _ _ _ _ Hx Hy))).
Qed.

Definition src_leq_divceil2r : Prop := ltac:(type_of_term @leq_divceil2r).
Definition tgt_leq_divceil2r : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_leq_divceil2r).
Theorem leq_divceil2r_correspondence : PropSPropRel src_leq_divceil2r tgt_leq_divceil2r.
Proof.
  unfold src_leq_divceil2r, tgt_leq_divceil2r.
  apply: ct_forall_nat => d dL Hd. apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn.
  apply: ct_imp; first exact (clt _ _ _ _ c0 Hd).
  exact (ct_imp _ _ _ _ (cle _ _ _ _ Hm Hn) (cle _ _ _ _ (cd_ceil _ _ _ _ Hm Hd) (cd_ceil _ _ _ _ Hn Hd))).
Qed.

Definition src_eq_modDl : Prop := ltac:(type_of_term @eq_modDl).
Definition tgt_eq_modDl : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_eq_modDl).
Theorem eq_modDl_correspondence : PropSPropRel src_eq_modDl tgt_eq_modDl.
Proof.
  unfold src_eq_modDl, tgt_eq_modDl.
  apply: ct_forall_nat => p pL Hp. apply: ct_forall_nat => m mL Hm.
  apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => d dL Hd.
  exact (cd_iff _ _ _ _ (ceq _ _ _ _ (cmod _ _ _ _ (cadd _ _ _ _ Hp Hm) Hd) (cmod _ _ _ _ (cadd _ _ _ _ Hp Hn) Hd))
           (ceq _ _ _ _ (cmod _ _ _ _ Hm Hd) (cmod _ _ _ _ Hn Hd))).
Qed.

Definition src_eq_modDr : Prop := ltac:(type_of_term @eq_modDr).
Definition tgt_eq_modDr : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_eq_modDr).
Theorem eq_modDr_correspondence : PropSPropRel src_eq_modDr tgt_eq_modDr.
Proof.
  unfold src_eq_modDr, tgt_eq_modDr.
  apply: ct_forall_nat => p pL Hp. apply: ct_forall_nat => m mL Hm.
  apply: ct_forall_nat => n nL Hn. apply: ct_forall_nat => d dL Hd.
  exact (cd_iff _ _ _ _ (ceq _ _ _ _ (cmod _ _ _ _ (cadd _ _ _ _ Hm Hp) Hd) (cmod _ _ _ _ (cadd _ _ _ _ Hn Hp) Hd))
           (ceq _ _ _ _ (cmod _ _ _ _ Hm Hd) (cmod _ _ _ _ Hn Hd))).
Qed.

Definition src_modulo_exists : Prop := ltac:(type_of_term @modulo_exists).
Definition tgt_modulo_exists : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_modulo_exists).
Theorem modulo_exists_correspondence : PropSPropRel src_modulo_exists tgt_modulo_exists.
Proof.
  unfold src_modulo_exists, tgt_modulo_exists.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => c cL Hc.
  apply: ct_imp; first exact (clt _ _ _ _ c0 Hc).
  apply: ct_imp; first exact (ceq _ _ _ _ (cmod _ _ _ _ Ha Hc) (cmod _ _ _ _ (cadd _ _ _ _ Hb Ha) Hc)).
  apply: ct_exists_nat => k kL Hk. exact (ceq _ _ _ _ Hb (cmul _ _ _ _ Hk Hc)).
Qed.

Definition src_modnS_eq : Prop := ltac:(type_of_term @modnS_eq).
Definition tgt_modnS_eq : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_modnS_eq).
Theorem modnS_eq_correspondence : PropSPropRel src_modnS_eq tgt_modnS_eq.
Proof.
  unfold src_modnS_eq, tgt_modnS_eq.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => n nL Hn.
  have Ha1 := csucc _ _ Ha. have Hn1 := csucc _ _ Hn.
  exact (cd_iff _ _ _ _ (ceq _ _ _ _ (cmod _ _ _ _ Ha1 Hn1) c0) (ceq _ _ _ _ (cmod _ _ _ _ Ha Hn1) Hn)).
Qed.

Definition src_modnSor' : Prop := ltac:(type_of_term @modnSor').
Definition tgt_modnSor' : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_modnSor').
Theorem modnSor'_correspondence : PropSPropRel src_modnSor' tgt_modnSor'.
Proof.
  unfold src_modnSor', tgt_modnSor'.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => n nL Hn. have Ha1 := csucc _ _ Ha.
  exact (ct_or _ _ _ _ (ceq _ _ _ _ (cmod _ _ _ _ Ha1 Hn) (csucc _ _ (cmod _ _ _ _ Ha Hn)))
           (ceq _ _ _ _ (cmod _ _ _ _ Ha1 Hn) c0)).
Qed.

Definition src_modnSor : Prop := ltac:(type_of_term @modnSor).
Definition tgt_modnSor : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_modnSor).
Theorem modnSor_correspondence : PropSPropRel src_modnSor tgt_modnSor.
Proof.
  unfold src_modnSor, tgt_modnSor.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => n nL Hn.
  have Ha1 := csucc _ _ Ha. have Hn1 := csucc _ _ Hn.
  exact (ct_or _ _ _ _ (ceq _ _ _ _ (cmod _ _ _ _ Ha1 Hn1) (csucc _ _ (cmod _ _ _ _ Ha Hn1)))
           (ceq _ _ _ _ (cmod _ _ _ _ Ha1 Hn1) c0)).
Qed.

Definition src_modulo_cases : Prop := ltac:(type_of_term @modulo_cases).
Definition tgt_modulo_cases : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_modulo_cases).
Theorem modulo_cases_correspondence : PropSPropRel src_modulo_cases tgt_modulo_cases.
Proof.
  unfold src_modulo_cases, tgt_modulo_cases.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => c cL Hc.
  have Ha1 := csucc _ _ Ha. have Hc1 := csucc _ _ Hc.
  apply: ct_or; first exact (ceq _ _ _ _ (cmod _ _ _ _ Ha1 Hc1) (csucc _ _ (cmod _ _ _ _ Ha Hc1))).
  exact (ct_and _ _ _ _ (ceq _ _ _ _ (cmod _ _ _ _ Ha1 Hc1) c0) (ceq _ _ _ _ (cmod _ _ _ _ Ha Hc1) Hc)).
Qed.

Definition src_ceil_eq1 : Prop := ltac:(type_of_term @ceil_eq1).
Definition tgt_ceil_eq1 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_ceil_eq1).
Theorem ceil_eq1_correspondence : PropSPropRel src_ceil_eq1 tgt_ceil_eq1.
Proof.
  unfold src_ceil_eq1, tgt_ceil_eq1.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => c cL Hc.
  apply: ct_imp; first exact (clt _ _ _ _ c0 Ha).
  exact (ct_imp _ _ _ _ (cle _ _ _ _ Ha Hc) (ceq _ _ _ _ (cd_ceil _ _ _ _ Ha Hc) c1)).
Qed.

Definition src_ceil_suba : Prop := ltac:(type_of_term @ceil_suba).
Definition tgt_ceil_suba : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_ceil_suba).
Theorem ceil_suba_correspondence : PropSPropRel src_ceil_suba tgt_ceil_suba.
Proof.
  unfold src_ceil_suba, tgt_ceil_suba.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => c cL Hc.
  apply: ct_imp; first exact (clt _ _ _ _ c0 Hc).
  exact (ct_imp _ _ _ _ (clt _ _ _ _ Hc Ha)
           (ceq _ _ _ _ (cd_ceil _ _ _ _ Ha Hc) (csucc _ _ (cd_ceil _ _ _ _ (csub _ _ _ _ Ha Hc) Hc)))).
Qed.

Definition src_mod_eq : Prop := ltac:(type_of_term @mod_eq).
Definition tgt_mod_eq : SProp := ltac:(type_of_term I.Prosa_Classic_Util_DivMod_mod_eq).
Theorem mod_eq_correspondence : PropSPropRel src_mod_eq tgt_mod_eq.
Proof.
  unfold src_mod_eq, tgt_mod_eq.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb.
  exact (ceq _ _ _ _ (cmod _ _ _ _ Ha Hb) (csub _ _ _ _ Ha (cmul _ _ _ _ (cdiv _ _ _ _ Ha Hb) Hb))).
Qed.
