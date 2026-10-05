(** Correspondences for [implementation/refinements/FP/refinements.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (unchanged).  The base
    maps and definition correspondences are those of the accepted refinements.v, arrival_bound.v, task.v,
    arrival_curve.v, arrival_curve_prefix.v, fast_search_space_computation.v and FP/fast_search_space.v certificates,
    re-bound in [RrBase] … [RrFPFastSearchSpace].  Here:
    - the seven generic definitions are related for related inputs (element types by identity, task lists by the
      generic task map, operation-class instances by their field, the task equality instance by its test);
    - the definitions at the binary numbers ([iota_N], the search spaces) and the five equality instances are related
      through the binary-number maps;
    - the generic definitions at [N] (with the [N] instances and this file's [eq_task]) are related through the
      binary-number maps;
    - the thirteen refinement instances are related by [TypeCorrespondence], through builders for each shape of
      relation ([list_R Rtask], [Rtask], [Rnat], [prod_R Rnat Rnat], [bool_R], [list_R Rnat] and their
      [hrespectful] combinations, and the shapes quantified over binary tasks).
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.FP.refinements.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefFPRefinements ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RrBase
  RrArrivalBound RrTask RrArrivalCurve RrArrivalCurvePrefix RrFastSearchSpaceComputation RrFPFastSearchSpace.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefFPRefinements.
Module Rr := prosa.implementation.refinements.FP.refinements.
Module Ffs := prosa.implementation.refinements.FP.fast_search_space.
Module Rac := prosa.implementation.refinements.arrival_curve.
Module Rt := prosa.implementation.refinements.task.
Module Rab := prosa.implementation.refinements.arrival_bound.
Module Dt := prosa.implementation.definitions.task.

Abbreviation IFRhep := I.Prosa_Implementation_Refinements_FP_Refinements_hep_task_T.
Abbreviation IFRthep := I.Prosa_Implementation_Refinements_FP_Refinements_total_hep_rbf_T.
Abbreviation IFRohep := I.Prosa_Implementation_Refinements_FP_Refinements_ohep_task_T.
Abbreviation IFRtohep := I.Prosa_Implementation_Refinements_FP_Refinements_total_ohep_rbf_T.
Abbreviation IFRcpFP := I.Prosa_Implementation_Refinements_FP_Refinements_check_point_FP_T.
Abbreviation IFRbb := I.Prosa_Implementation_Refinements_FP_Refinements_blocking_bound_NP_T.
Abbreviation IFRcpNP := I.Prosa_Implementation_Refinements_FP_Refinements_check_point_NP_T.
Abbreviation IFRiota := I.Prosa_Implementation_Refinements_FP_Refinements_iota_N.
Abbreviation IFRsshN := I.Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_h_N.
Abbreviation IFRssN := I.Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_N.
Abbreviation IFReqL := I.Prosa_Implementation_Refinements_FP_Refinements_eq_listN.
Abbreviation IFReqLL := I.Prosa_Implementation_Refinements_FP_Refinements_eq_listNN.
Abbreviation IFReqP := I.Prosa_Implementation_Refinements_FP_Refinements_eq_NlistNN.
Abbreviation IFReqAB := I.Prosa_Implementation_Refinements_FP_Refinements_eq_taskab.
Abbreviation IFReqT := I.Prosa_Implementation_Refinements_FP_Refinements_eq_task.
Abbreviation INsubI := I.Prosa_Implementation_Refinements_Refinements_sub_N.
Abbreviation ITtt := I.Prosa_Implementation_Refinements_Task_taskT_to_task.
Abbreviation ITrbf := I.Prosa_Implementation_Refinements_Task_task_rbf_T.

(** ** Small components *)
Lemma rf_not_ex b : Lean.eq (be (~~ b)) (I.Bool_not (be b)).
Proof. destruct b; exact (rf_refl _). Qed.

Definition rf_congr3 {A B C D : Type} (f : A -> B -> C -> D) a a' b b' c c' (Ha : Lean.eq a a') (Hb : Lean.eq b b')
    (Hc : Lean.eq c c') : Lean.eq (f a b c) (f a' b' c') :=
  rf_trans _ _ _ (rf_congr2 (fun x y => f x y c) _ _ _ _ Ha Hb) (rf_congr (f a' b') _ _ Hc).

Definition rf_congr4 {A B C D E : Type} (f : A -> B -> C -> D -> E) a a' b b' c c' d d' (Ha : Lean.eq a a')
    (Hb : Lean.eq b b') (Hc : Lean.eq c c') (Hd : Lean.eq d d') : Lean.eq (f a b c d) (f a' b' c' d') :=
  rf_trans _ _ _ (rf_congr3 (fun x y z => f x y z d) _ _ _ _ _ _ Ha Hb Hc) (rf_congr (f a' b' c') _ _ Hd).

(** [foldr] of a [map] of a [filter], related through element maps. *)
Lemma rf_fmf_ex {A C T TL : Type} (eA : A -> C) (eT : T -> TL) (f : T -> T -> T) (fL : TL -> TL -> TL)
    (Hf : forall a b, Lean.eq (eT (f a b)) (fL (eT a) (eT b))) (z : T) zL (Hz : Lean.eq (eT z) zL)
    (g : A -> T) (gL : C -> TL) (Hg : forall x, Lean.eq (eT (g x)) (gL (eA x)))
    (p : A -> bool) (pL : C -> I.Bool) (Hp : forall x, Lean.eq (be (p x)) (pL (eA x))) xs :
  Lean.eq (eT (foldr f z (map g (filter p xs))))
    (I.List_foldr_inst3 TL TL fL zL (I.List_map_inst3 C TL gL (I.List_filter_inst1 C pL (lex eA xs)))).
Proof.
  refine (rf_trans _ _ _ (rf_foldr_ex eT eT f fL Hf z _) (rf_congr2 (I.List_foldr_inst3 TL TL fL) _ _ _ _ Hz _)).
  refine (rf_trans _ _ _ (rf_map_ex eA eT g gL Hg _) (rf_congr (I.List_map_inst3 C TL gL) _ _ _)).
  exact (rf_filter_ex eA p pL Hp xs).
Qed.

(** ** The generic definitions (element types by identity, operation classes by their field) *)
Definition EqTRel {T : Type} (eR : eq_of (@Rt.task_T T)) (eL : Ieq_of (ITT T)) : SProp :=
  forall x y, Lean.eq (be (eR x y)) (Ieq_op (ITT T) eL (taskT_ex idr x) (taskT_ex idr y)).

Lemma rf_hepT_ex (T : Type) (lR : leq_of T) lL : BOpRel lR (Ileq_op T lL) -> forall t1 t2,
  Lean.eq (be (@Rr.hep_task_T T lR t1 t2)) (IFRhep T lL (taskT_ex idr t1) (taskT_ex idr t2)).
Proof. intros Hl t1 t2. exact (Hl _ _). Qed.

Lemma hep_task_T_correspondence (T : Type) (lR : leq_of T) lL : BOpRel lR (Ileq_op T lL) ->
  forall t1R t1L t2R t2L, TaskTRel t1R t1L -> TaskTRel t2R t2L ->
  Lean.eq (be (@Rr.hep_task_T T lR t1R t2R)) (IFRhep T lL t1L t2L).
Proof. intros Hl t1R t1L t2R t2L H1 H2. destruct H1. destruct H2. exact (rf_hepT_ex T lR lL Hl t1R t2R). Qed.

Lemma rf_ohepT_ex (T : Type) (lR : leq_of T) lL (eR : eq_of (@Rt.task_T T)) eL :
  BOpRel lR (Ileq_op T lL) -> EqTRel eR eL -> forall t1 t2,
  Lean.eq (be (@Rr.ohep_task_T T lR eR t1 t2)) (IFRohep T lL eL (taskT_ex idr t1) (taskT_ex idr t2)).
Proof.
  intros Hl He t1 t2. unfold Rr.ohep_task_T.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_hepT_ex T lR lL Hl t1 t2) _)).
  exact (rf_trans _ _ _ (rf_not_ex _) (rf_congr I.Bool_not _ _ (He t1 t2))).
Qed.

Lemma ohep_task_T_correspondence (T : Type) (lR : leq_of T) lL (eR : eq_of (@Rt.task_T T)) eL :
  BOpRel lR (Ileq_op T lL) -> EqTRel eR eL ->
  forall t1R t1L t2R t2L, TaskTRel t1R t1L -> TaskTRel t2R t2L ->
  Lean.eq (be (@Rr.ohep_task_T T lR eR t1R t2R)) (IFRohep T lL eL t1L t2L).
Proof. intros Hl He t1R t1L t2R t2L H1 H2. destruct H1. destruct H2. exact (rf_ohepT_ex T lR lL eR eL Hl He t1R t2R). Qed.

Section Generic.
  Context (T : Type) (zR : zero_of T) (zL : Izero_of T) (oR : one_of T) (oL : Ione_of T) (sR : sub_of T) (sL : Isub_of T)
    (aR : add_of T) (aL : Iadd_of T) (mR : mul_of T) (mL : I.Prosa_Implementation_Refinements_Refinements_mul_of T)
    (dR : div_of T) (dL : Idiv_of T) (moR : mod_of T) (moL : Imod_of T) (lR : leq_of T) (lL : Ileq_of T)
    (ltR : lt_of T) (ltL : Ilt_of T) (eR : eq_of (@Rt.task_T T)) (eL : Ieq_of (ITT T)).
  Context (Hz : ZeroRel zR zL) (Ho : OneRel oR oL) (Hs : Op2Rel sR (Isub_op T sL)) (Ha : Op2Rel aR (Iadd_op T aL))
    (Hm : Op2Rel mR (Imul_op T mL)) (Hd : Op2Rel dR (Idiv_op T dL)) (Hmo : Op2Rel moR (Imod_op T moL))
    (Hl : BOpRel lR (Ileq_op T lL)) (Hlt : BOpRel ltR (Ilt_op T ltL)) (He : EqTRel eR eL).

  Let Hrbf t d : Lean.eq (@Rt.task_rbf_T T zR oR aR mR dR moR lR t d) (ITrbf T zL oL aL mL dL moL lL (taskT_ex idr t) d) :=
    task_rbf_T_correspondence T zR zL oR oL aR aL mR mL dR dL moR moL lR lL Hz Ho Ha Hm Hd Hmo Hl t _ d d (rf_refl _) (rf_refl _).

  Lemma rf_thepT_ex ts t d :
    Lean.eq (@Rr.total_hep_rbf_T T zR oR aR mR dR moR lR ts t d)
      (IFRthep T zL oL aL mL dL moL lL (lex (taskT_ex idr) ts) (taskT_ex idr t) d).
  Proof.
    unfold Rr.total_hep_rbf_T. cbv zeta.
    exact (rf_fmf_ex (taskT_ex idr) idr _ _ (fun a b => Ha a b) _ _ Hz _ _ (fun x => Hrbf x d) _ _
      (fun x => rf_hepT_ex T lR lL Hl x t) ts).
  Qed.

  Lemma rf_tohepT_ex ts t d :
    Lean.eq (@Rr.total_ohep_rbf_T T zR oR aR mR dR moR lR eR ts t d)
      (IFRtohep T zL oL aL mL dL moL lL eL (lex (taskT_ex idr) ts) (taskT_ex idr t) d).
  Proof.
    unfold Rr.total_ohep_rbf_T. cbv zeta.
    exact (rf_fmf_ex (taskT_ex idr) idr _ _ (fun a b => Ha a b) _ _ Hz _ _ (fun x => Hrbf x d) _ _
      (fun x => rf_ohepT_ex T lR lL eR eL Hl He x t) ts).
  Qed.

  Lemma rf_cpFPT_ex ts t R p :
    Lean.eq (be (@Rr.check_point_FP_T T zR oR aR mR dR moR lR eR ts t R p))
      (IFRcpFP T zL oL aL mL dL moL lL eL (lex (taskT_ex idr) ts) (taskT_ex idr t) R (pre idr idr p)).
  Proof.
    destruct p as [a f]. unfold Rr.check_point_FP_T. cbn [fst snd].
    have Ho' : Lean.eq oR (Ione_op T oL) := Ho.
    refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (Hl f R))).
    refine (rf_trans _ _ _ (Hl _ _) (rf_congr2 (Ileq_op T lL) _ _ _ _ _ (Ha a f))).
    refine (rf_trans _ _ _ (Ha _ _) (rf_congr2 (Iadd_op T aL) _ _ _ _ _ _)).
    - refine (rf_trans _ _ _ (Hrbf t _) (rf_congr (ITrbf T zL oL aL mL dL moL lL (taskT_ex idr t)) _ _ _)).
      exact (rf_trans _ _ _ (Ha a oR) (rf_congr (Iadd_op T aL a) _ _ Ho')).
    - exact (rf_trans _ _ _ (rf_tohepT_ex ts t _) (rf_congr (IFRtohep T zL oL aL mL dL moL lL eL _ _) _ _ (Ha a f))).
  Qed.

  Lemma rf_bbT_ex ts t :
    Lean.eq (@Rr.blocking_bound_NP_T T zR oR sR lR ltR ts t)
      (IFRbb T zL oL sL lL ltL (lex (taskT_ex idr) ts) (taskT_ex idr t)).
  Proof.
    unfold Rr.blocking_bound_NP_T. cbv zeta.
    have Ho' : Lean.eq oR (Ione_op T oL) := Ho.
    refine (rf_fmf_ex (taskT_ex idr) idr _ _ (fun a b => maxn_T_correspondence T ltR ltL Hlt a a b b (rf_refl _) (rf_refl _))
      _ _ Hz _ _ _ _ _ (fun x => rf_trans _ _ _ (rf_not_ex _) (rf_congr I.Bool_not _ _ (rf_hepT_ex T lR lL Hl x t))) ts).
    intro x. exact (rf_trans _ _ _ (Hs _ _) (rf_congr (Isub_op T sL _) _ _ Ho')).
  Qed.

  Lemma rf_cpNPT_ex ts t R p :
    Lean.eq (be (@Rr.check_point_NP_T T zR oR sR aR mR dR moR lR ltR eR ts t R p))
      (IFRcpNP T zL oL sL aL mL dL moL lL ltL eL (lex (taskT_ex idr) ts) (taskT_ex idr t) R (pre idr idr p)).
  Proof.
    destruct p as [a f]. unfold Rr.check_point_NP_T. cbn [fst snd].
    have Ho' : Lean.eq oR (Ione_op T oL) := Ho.
    have Hc : Lean.eq (sR (Rt.task_cost_T t) oR) (Isub_op T sL (Rt.task_cost_T t) (Ione_op T oL)) :=
      rf_trans _ _ _ (Hs _ _) (rf_congr (Isub_op T sL _) _ _ Ho').
    refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
    - refine (rf_trans _ _ _ (Hl _ _) (rf_congr2 (Ileq_op T lL) _ _ _ _ _ (Ha a f))).
      refine (rf_trans _ _ _ (Ha _ _) (rf_congr2 (Iadd_op T aL) _ _ _ _ _ _)).
      + refine (rf_trans _ _ _ (Ha _ _) (rf_congr2 (Iadd_op T aL) _ _ _ _ (rf_bbT_ex ts t) _)).
        refine (rf_trans _ _ _ (Hs _ _) (rf_congr2 (Isub_op T sL) _ _ _ _ _ Hc)).
        refine (rf_trans _ _ _ (Hrbf t _) (rf_congr (ITrbf T zL oL aL mL dL moL lL (taskT_ex idr t)) _ _ _)).
        exact (rf_trans _ _ _ (Ha a oR) (rf_congr (Iadd_op T aL a) _ _ Ho')).
      + exact (rf_trans _ _ _ (rf_tohepT_ex ts t _) (rf_congr (IFRtohep T zL oL aL mL dL moL lL eL _ _) _ _ (Ha a f))).
    - refine (rf_trans _ _ _ (Hl _ _) (rf_congr (fun z => Ileq_op T lL z R) _ _ _)).
      exact (rf_trans _ _ _ (Ha _ _) (rf_congr (Iadd_op T aL f) _ _ Hc)).
  Qed.
End Generic.

Lemma total_hep_rbf_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL
    (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) ->
  forall tsR tsL tR tL dR' dL', Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq dR' dL' ->
  Lean.eq (@Rr.total_hep_rbf_T T zR oR aR mR dR moR lR tsR tR dR') (IFRthep T zL oL aL mL dL moL lL tsL tL dL').
Proof.
  intros Hz Ho Ha Hm Hd Hmo Hl tsR tsL tR tL dR' dL' Hs Ht Hd'. destruct Hs. destruct Ht. destruct Hd'.
  exact (rf_thepT_ex T zR zL oR oL aR aL mR mL dR dL moR moL lR lL Hz Ho Ha Hm Hd Hmo Hl tsR tR dR').
Qed.

Lemma total_ohep_rbf_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL
    (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL (eR : eq_of (@Rt.task_T T)) eL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> EqTRel eR eL ->
  forall tsR tsL tR tL dR' dL', Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq dR' dL' ->
  Lean.eq (@Rr.total_ohep_rbf_T T zR oR aR mR dR moR lR eR tsR tR dR') (IFRtohep T zL oL aL mL dL moL lL eL tsL tL dL').
Proof.
  intros Hz Ho Ha Hm Hd Hmo Hl He tsR tsL tR tL dR' dL' Hs Ht Hd'. destruct Hs. destruct Ht. destruct Hd'.
  exact (rf_tohepT_ex T zR zL oR oL aR aL mR mL dR dL moR moL lR lL eR eL Hz Ho Ha Hm Hd Hmo Hl He tsR tR dR').
Qed.

Lemma check_point_FP_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL
    (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL (eR : eq_of (@Rt.task_T T)) eL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> EqTRel eR eL ->
  forall tsR tsL tR tL RR RL pR pL, Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq RR RL ->
  Lean.eq (pre idr idr pR) pL ->
  Lean.eq (be (@Rr.check_point_FP_T T zR oR aR mR dR moR lR eR tsR tR RR pR)) (IFRcpFP T zL oL aL mL dL moL lL eL tsL tL RL pL).
Proof.
  intros Hz Ho Ha Hm Hd Hmo Hl He tsR tsL tR tL RR RL pR pL Hs Ht HR Hp. destruct Hs. destruct Ht. destruct HR. destruct Hp.
  exact (rf_cpFPT_ex T zR zL oR oL aR aL mR mL dR dL moR moL lR lL eR eL Hz Ho Ha Hm Hd Hmo Hl He tsR tR RR pR).
Qed.

Lemma blocking_bound_NP_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (sR : sub_of T) sL
    (lR : leq_of T) lL (ltR : lt_of T) ltL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel sR (Isub_op T sL) -> BOpRel lR (Ileq_op T lL) -> BOpRel ltR (Ilt_op T ltL) ->
  forall tsR tsL tR tL, Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL ->
  Lean.eq (@Rr.blocking_bound_NP_T T zR oR sR lR ltR tsR tR) (IFRbb T zL oL sL lL ltL tsL tL).
Proof.
  intros Hz Ho Hs Hl Hlt tsR tsL tR tL Hts Ht. destruct Hts. destruct Ht.
  exact (rf_bbT_ex T zR zL oR oL sR sL lR lL ltR ltL Hz Ho Hs Hl Hlt tsR tR).
Qed.

Lemma check_point_NP_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (sR : sub_of T) sL
    (aR : add_of T) aL (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL
    (ltR : lt_of T) ltL (eR : eq_of (@Rt.task_T T)) eL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel sR (Isub_op T sL) -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) ->
  Op2Rel dR (Idiv_op T dL) -> Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> BOpRel ltR (Ilt_op T ltL) ->
  EqTRel eR eL ->
  forall tsR tsL tR tL RR RL pR pL, Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq RR RL ->
  Lean.eq (pre idr idr pR) pL ->
  Lean.eq (be (@Rr.check_point_NP_T T zR oR sR aR mR dR moR lR ltR eR tsR tR RR pR))
    (IFRcpNP T zL oL sL aL mL dL moL lL ltL eL tsL tL RL pL).
Proof.
  intros Hz Ho Hs Ha Hm Hd Hmo Hl Hlt He tsR tsL tR tL RR RL pR pL Hts Ht HR Hp.
  destruct Hts. destruct Ht. destruct HR. destruct Hp.
  exact (rf_cpNPT_ex T zR zL oR oL sR sL aR aL mR mL dR dL moR moL lR lL ltR ltL eR eL Hz Ho Hs Ha Hm Hd Hmo Hl Hlt He
    tsR tR RR pR).
Qed.

(** ** The equality instances *)
Lemma rf_FReqL_ex x y : Lean.eq (be (Rr.eq_listN x y)) (Ieq_op (IList IN) IFReqL (lex Ne_ x) (lex Ne_ y)).
Proof. exact (rf_decide_ex _ _ _ (rf_eqtype_rel (lex Ne_) (lim Ni) (rf_lim_lex Ne_ Ni rf_Ni_Ne) x y)). Qed.

Lemma eq_listN_correspondence xR xL yR yL :
  Lean.eq (lex Ne_ xR) xL -> Lean.eq (lex Ne_ yR) yL -> Lean.eq (be (Rr.eq_listN xR yR)) (Ieq_op (IList IN) IFReqL xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_FReqL_ex xR yR). Qed.

Lemma rf_FReqLL_ex x y :
  Lean.eq (be (Rr.eq_listNN x y)) (Ieq_op (IList (IProd IN IN)) IFReqLL (lex (pre Ne_ Ne_) x) (lex (pre Ne_ Ne_) y)).
Proof.
  exact (rf_decide_ex _ _ _ (rf_eqtype_rel (lex (pre Ne_ Ne_)) (lim (pri Ni Ni))
    (rf_lim_lex (pre Ne_ Ne_) (pri Ni Ni) rf_pri_pre_N) x y)).
Qed.

Lemma eq_listNN_correspondence xR xL yR yL :
  Lean.eq (lex (pre Ne_ Ne_) xR) xL -> Lean.eq (lex (pre Ne_ Ne_) yR) yL ->
  Lean.eq (be (Rr.eq_listNN xR yR)) (Ieq_op (IList (IProd IN IN)) IFReqLL xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_FReqLL_ex xR yR). Qed.

Lemma rf_FReqP_ex x y :
  Lean.eq (be (Rr.eq_NlistNN x y)) (Ieq_op (IProd IN (IList (IProd IN IN))) IFReqP (pfx Ne_ x) (pfx Ne_ y)).
Proof. exact (rf_eq_NlistNN_ex x y). Qed.

Lemma eq_NlistNN_correspondence xR xL yR yL :
  Lean.eq (pfx Ne_ xR) xL -> Lean.eq (pfx Ne_ yR) yL ->
  Lean.eq (be (Rr.eq_NlistNN xR yR)) (Ieq_op (IProd IN (IList (IProd IN IN))) IFReqP xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_FReqP_ex xR yR). Qed.

Lemma rf_FReqAB_ex x y : Lean.eq (be (Rr.eq_taskab x y)) (Ieq_op (ITab IN) IFReqAB (tabT_ex Ne_ x) (tabT_ex Ne_ y)).
Proof. exact (rf_eq_taskab_ex x y). Qed.

Lemma eq_taskab_correspondence xR xL yR yL :
  Lean.eq (tabT_ex Ne_ xR) xL -> Lean.eq (tabT_ex Ne_ yR) yL ->
  Lean.eq (be (Rr.eq_taskab xR yR)) (Ieq_op (ITab IN) IFReqAB xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_FReqAB_ex xR yR). Qed.

Lemma rf_FReqT_ex x y : Lean.eq (be (Rr.eq_task x y)) (Ieq_op (ITT IN) IFReqT (taskT_ex Ne_ x) (taskT_ex Ne_ y)).
Proof.
  destruct x as [i1 c1 a1 d1 p1]; destruct y as [i2 c2 a2 d2 p2].
  change (Lean.eq (be (Rt.task_eqdef_T (Rt.Build_task_T i1 c1 a1 d1 p1) (Rt.Build_task_T i2 c2 a2 d2 p2)))
    (Ieq_op (ITT IN) IFReqT (taskT_ex Ne_ (Rt.Build_task_T i1 c1 a1 d1 p1)) (taskT_ex Ne_ (Rt.Build_task_T i2 c2 a2 d2 p2)))).
  unfold Rt.task_eqdef_T. cbn.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_N_eqb_ex p1 p2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_N_eqb_ex d1 d2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_FReqAB_ex a1 a2))).
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_N_eqb_ex i1 i2) (rf_N_eqb_ex c1 c2))).
Qed.

Lemma eq_task_correspondence xR xL yR yL :
  Lean.eq (taskT_ex Ne_ xR) xL -> Lean.eq (taskT_ex Ne_ yR) yL ->
  Lean.eq (be (Rr.eq_task xR yR)) (Ieq_op (ITT IN) IFReqT xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_FReqT_ex xR yR). Qed.

(** ** Definitions at the binary numbers *)
Lemma rf_iotaN_ex a d : Lean.eq (lex Ne_ (Rr.iota_N a d)) (IFRiota (Ne_ a) (Ne_ d)).
Proof.
  exact (rf_trans _ _ _ (rf_iota_T_N_ex a (nat_of_bin d))
    (rf_congr (I.Prosa_Implementation_Refinements_Refinements_iota_T IN IN1 INaddI (Ne_ a)) _ _ (rf_nat_of_bin_ex d))).
Qed.

Lemma iota_N_correspondence aR aL dR dL :
  Lean.eq (Ne_ aR) aL -> Lean.eq (Ne_ dR) dL -> Lean.eq (lex Ne_ (Rr.iota_N aR dR)) (IFRiota aL dL).
Proof. intros Ha Hd. destruct Ha. destruct Hd. exact (rf_iotaN_ex aR dR). Qed.

Lemma rf_sshN_ex t l r : Lean.eq (lex Ne_ (Rr.search_space_emax_FP_h_N t l r)) (IFRsshN (taskT_ex Ne_ t) (Ne_ l) (Ne_ r)).
Proof.
  unfold Rr.search_space_emax_FP_h_N. cbv zeta.
  refine (rf_trans _ _ _ (rf_map_ex Ne_ Ne_ _ _ rf_predn_T_N_ex _) (rf_congr (I.List_map_inst3 IN IN _) _ _ _)).
  refine (rf_trans _ _ _ (rf_rswoT_N_ex t _) (rf_congr (I.Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T IN
    IN1 INaddI (taskT_ex Ne_ t)) _ _ _)).
  refine (rf_trans _ _ _ (rf_map_ex Ne_ Ne_ _ (INmul (I.Prosa_Implementation_Refinements_Task_get_horizon_of_task_T IN IN1
    (taskT_ex Ne_ t))) (fun i => rf_trans _ _ _ (rf_N_mul_ex _ i) (rf_congr (fun h => INmul h (Ne_ i)) _ _ (rf_ghotT_N_ex t))) _)
    (rf_congr (I.List_map_inst3 IN IN _) _ _ (rf_iotaN_ex l r))).
Qed.

Lemma search_space_emax_FP_h_N_correspondence tR tL lR lL rR rL :
  Lean.eq (taskT_ex Ne_ tR) tL -> Lean.eq (Ne_ lR) lL -> Lean.eq (Ne_ rR) rL ->
  Lean.eq (lex Ne_ (Rr.search_space_emax_FP_h_N tR lR rR)) (IFRsshN tL lL rL).
Proof. intros Ht Hl Hr. destruct Ht. destruct Hl. destruct Hr. exact (rf_sshN_ex tR lR rR). Qed.

Lemma rf_ssN_ex t L : Lean.eq (lex Ne_ (Rr.search_space_emax_FP_N t L)) (IFRssN (taskT_ex Ne_ t) (Ne_ L)).
Proof.
  unfold Rr.search_space_emax_FP_N. cbv zeta.
  refine (rf_trans _ _ _ (rf_sshN_ex t _ _) (rf_congr (IFRsshN (taskT_ex Ne_ t) (Ne_ N0)) _ _ _)).
  refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr (fun z => INadd z (Ne_ (Npos xH))) _ _ _)).
  exact (rf_trans _ _ _ (rf_N_div_ex _ _) (rf_congr (INdiv (Ne_ L)) _ _ (rf_ghotT_N_ex t))).
Qed.

Lemma search_space_emax_FP_N_correspondence tR tL LR LL :
  Lean.eq (taskT_ex Ne_ tR) tL -> Lean.eq (Ne_ LR) LL ->
  Lean.eq (lex Ne_ (Rr.search_space_emax_FP_N tR LR)) (IFRssN tL LL).
Proof. intros Ht HL. destruct Ht. destruct HL. exact (rf_ssN_ex tR LR). Qed.

(** ** The generic definitions at [N] (with the [N] instances and this file's [eq_task]) *)
Lemma rf_hepT_N_ex t1 t2 :
  Lean.eq (be (Rr.hep_task_T t1 t2)) (IFRhep IN INleqI (taskT_ex Ne_ t1) (taskT_ex Ne_ t2)).
Proof. exact (rf_N_leb_ex _ _). Qed.

Lemma rf_ohepT_N_ex t1 t2 :
  Lean.eq (be (Rr.ohep_task_T t1 t2)) (IFRohep IN INleqI IFReqT (taskT_ex Ne_ t1) (taskT_ex Ne_ t2)).
Proof.
  unfold Rr.ohep_task_T.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_hepT_N_ex t1 t2) _)).
  exact (rf_trans _ _ _ (rf_not_ex _) (rf_congr I.Bool_not _ _ (rf_FReqT_ex t1 t2))).
Qed.

Lemma rf_thepT_N_ex ts t d :
  Lean.eq (Ne_ (Rr.total_hep_rbf_T ts t d))
    (IFRthep IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ d)).
Proof.
  unfold Rr.total_hep_rbf_T. cbv zeta.
  exact (rf_fmf_ex (taskT_ex Ne_) Ne_ _ _ rf_N_add_ex _ _ (rf_refl _) _ _ (fun x => rf_rbfT_N_ex x d) _ _
    (fun x => rf_hepT_N_ex x t) ts).
Qed.

Lemma rf_tohepT_N_ex ts t d :
  Lean.eq (Ne_ (Rr.total_ohep_rbf_T ts t d))
    (IFRtohep IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI IFReqT (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ d)).
Proof.
  unfold Rr.total_ohep_rbf_T. cbv zeta.
  exact (rf_fmf_ex (taskT_ex Ne_) Ne_ _ _ rf_N_add_ex _ _ (rf_refl _) _ _ (fun x => rf_rbfT_N_ex x d) _ _
    (fun x => rf_ohepT_N_ex x t) ts).
Qed.

Lemma rf_cpFPT_N_ex ts t R p :
  Lean.eq (be (Rr.check_point_FP_T ts t R p))
    (IFRcpFP IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI IFReqT (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ R)
       (pre Ne_ Ne_ p)).
Proof.
  destruct p as [a f]. unfold Rr.check_point_FP_T. cbn [fst snd].
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_N_leb_ex f R))).
  refine (rf_trans _ _ _ (rf_N_leb_ex _ _) (rf_congr2 INleb _ _ _ _ _ (rf_N_add_ex a f))).
  refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr2 INadd _ _ _ _ _ _)).
  - exact (rf_trans _ _ _ (rf_rbfT_N_ex t _) (rf_congr (ITrbf IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI (taskT_ex Ne_ t))
      _ _ (rf_N_add_ex a (Npos xH)))).
  - exact (rf_trans _ _ _ (rf_tohepT_N_ex ts t _) (rf_congr (IFRtohep IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI IFReqT _ _)
      _ _ (rf_N_add_ex a f))).
Qed.

Lemma rf_bbT_N_ex ts t :
  Lean.eq (Ne_ (Rr.blocking_bound_NP_T ts t)) (IFRbb IN IN0 IN1 INsubI INleqI INltI (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t)).
Proof.
  unfold Rr.blocking_bound_NP_T. cbv zeta.
  refine (rf_fmf_ex (taskT_ex Ne_) Ne_ _ _ rf_maxn_T_N_ex _ _ (rf_refl _) _ _ _ _ _
    (fun x => rf_trans _ _ _ (rf_not_ex _) (rf_congr I.Bool_not _ _ (rf_hepT_N_ex x t))) ts).
  intro x. exact (rf_N_sub_ex _ _).
Qed.

Lemma rf_cpNPT_N_ex ts t R p :
  Lean.eq (be (Rr.check_point_NP_T ts t R p))
    (IFRcpNP IN IN0 IN1 INsubI INaddI INmulI INdivI INmodI INleqI INltI IFReqT (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t)
       (Ne_ R) (pre Ne_ Ne_ p)).
Proof.
  destruct p as [a f]. unfold Rr.check_point_NP_T. cbn [fst snd].
  have Hc := rf_N_sub_ex (Rt.task_cost_T t) (Npos xH).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
  - refine (rf_trans _ _ _ (rf_N_leb_ex _ _) (rf_congr2 INleb _ _ _ _ _ (rf_N_add_ex a f))).
    refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr2 INadd _ _ _ _ _ _)).
    + refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr2 INadd _ _ _ _ (rf_bbT_N_ex ts t) _)).
      refine (rf_trans _ _ _ (rf_N_sub_ex _ _) (rf_congr2 INsub _ _ _ _ _ Hc)).
      exact (rf_trans _ _ _ (rf_rbfT_N_ex t _) (rf_congr (ITrbf IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI (taskT_ex Ne_ t))
        _ _ (rf_N_add_ex a (Npos xH)))).
    + exact (rf_trans _ _ _ (rf_tohepT_N_ex ts t _) (rf_congr (IFRtohep IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI IFReqT _ _)
        _ _ (rf_N_add_ex a f))).
  - refine (rf_trans _ _ _ (rf_N_leb_ex _ _) (rf_congr (fun z => INleb z (Ne_ R)) _ _ _)).
    exact (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr (INadd (Ne_ f)) _ _ Hc)).
Qed.

(** ** The natural-number side: the task equality *)
Lemma rf_task_eqdef_ex t1 t2 :
  Lean.eq (be (Dt.task_eqdef t1 t2)) (I.Prosa_Implementation_Definitions_Task_task_eqdef (task_ex t1) (task_ex t2)).
Proof.
  destruct t1 as [i1 c1 a1 d1 p1]; destruct t2 as [i2 c2 a2 d2 p2]. unfold Dt.task_eqdef. cbn.
  have Hn := fun a b => rf_decide_ex _ _ (I.instDecidableEqNat (ne a) (ne b)) (rf_eqn_rel a b).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (Hn p1 p2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (Hn d1 d2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _
    (rf_decide_ex _ _ _ (rf_eqtype_rel ab_ex ab_im rf_ab_rt a1 a2)))).
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (Hn i1 i2) (Hn c1 c2))).
Qed.

(** ** Builders for the refinement statements *)
Abbreviation IlRt := (IlR ICT (ITT IN) IRtask).
Definition ltR_fw := listR_fw task_ex (taskT_ex Ne_) Rt.Rtask IRtask rtask_fw.
Definition ltR_bw := listR_bw task_im (taskT_im Ni) Rt.Rtask IRtask rtask_bw.
Definition rf_lt_rtL := rf_lex_lim task_ex task_im rf_task_rtL.
Definition rf_ltT_rtL := rf_lex_lim (taskT_ex Ne_) (taskT_im Ni) (rf_taskT_rtL Ne_ Ni rf_Ne_Ni).
Definition rf_lt_rt := rf_lim_lex task_ex task_im rf_task_rt.
Definition rf_ltT_rt := rf_lim_lex (taskT_ex Ne_) (taskT_im Ni) (rf_taskT_rt Ne_ Ni rf_Ni_Ne).

(** [list_R Rtask ==> Rtask ==> R] with a result relation [R] mapped both ways. *)
Definition rf_corr_lt {C C' CL C'L : Type} (eC : C -> CL) (eC' : C' -> C'L) (iC : CL -> C) (iC' : C'L -> C')
    (S : C -> C' -> Type) (SL : CL -> C'L -> Type)
    (fwS : forall b b', S b b' -> SL (eC b) (eC' b')) (bwS : forall c c', SL c c' -> S (iC c) (iC' c'))
    (rtC : forall b, iC (eC b) = b) (rtC' : forall b, iC' (eC' b) = b)
    (f : seq Dt.concrete_task -> Dt.concrete_task -> C) (g : seq (@Rt.task_T N) -> @Rt.task_T N -> C')
    (fL : IList ICT -> ICT -> CL) (gL : IList (ITT IN) -> ITT IN -> C'L)
    (Hf : forall ts t, Lean.eq (eC (f ts t)) (fL (lex task_ex ts) (task_ex t)))
    (Hg : forall ts t, Lean.eq (eC' (g ts t)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t))) :
  TypeCorrespondence (refines (hrespectful (list_R Rt.Rtask) (hrespectful Rt.Rtask S)) f g)
    (Iref _ _ (Ihr (IList ICT) (IList (ITT IN)) _ _ IlRt (Ihr ICT (ITT IN) CL C'L IRtask SL)) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros tsL tsL' rts tL tL' rt.
    have o := fwS _ _ (rf_ref_out s _ _ (ltR_bw _ _ rts) _ _ (rtask_bw _ _ rt)).
    refine (rf_tr2 SL _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (rf_lt_rtL tsL) (rf_task_rtL tL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_ltT_rtL tsL') (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL'))).
  - intro t. apply rf_ref_in. intros ts ts' rts u u' ru.
    have o := Iref_rel _ _ _ _ _ t _ _ (ltR_fw _ _ rts) _ _ (rtask_fw _ _ ru).
    have o' := bwS _ _ (rf_tr2 SL (rf_sym _ _ (Hf ts u)) (rf_sym _ _ (Hg ts' u')) o).
    by rewrite rtC rtC' in o'.
Defined.

(** [forall ts tsk, refines R (f (map taskT_to_task ts) (taskT_to_task tsk)) (g ts tsk)]. *)
Definition rf_corr_TT {C C' CL C'L : Type} (eC : C -> CL) (eC' : C' -> C'L) (iC : CL -> C) (iC' : C'L -> C')
    (S : C -> C' -> Type) (SL : CL -> C'L -> Type)
    (fwS : forall b b', S b b' -> SL (eC b) (eC' b')) (bwS : forall c c', SL c c' -> S (iC c) (iC' c'))
    (rtC : forall b, iC (eC b) = b) (rtC' : forall b, iC' (eC' b) = b)
    (f : seq Dt.concrete_task -> Dt.concrete_task -> C) (g : seq (@Rt.task_T N) -> @Rt.task_T N -> C')
    (fL : IList ICT -> ICT -> CL) (gL : IList (ITT IN) -> ITT IN -> C'L)
    (Hf : forall ts t, Lean.eq (eC (f ts t)) (fL (lex task_ex ts) (task_ex t)))
    (Hg : forall ts t, Lean.eq (eC' (g ts t)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t))) :
  TypeCorrespondence
    (forall (ts : seq (@Rt.task_T N)) (tsk : @Rt.task_T N), refines S (f (map Rt.taskT_to_task ts) (Rt.taskT_to_task tsk)) (g ts tsk))
    (forall (ts : IList (ITT IN)) (tsk : ITT IN), Iref _ _ SL (fL (I.List_map_inst3 (ITT IN) ICT ITtt ts) (ITtt tsk)) (gL ts tsk)).
Proof.
  have Hm := fun ts => rf_map_ex (taskT_ex Ne_) task_ex Rt.taskT_to_task ITtt rf_taskT2task_ex ts.
  split.
  - intros s tsL tL. apply Iref_mk.
    have o := fwS _ _ (rf_ref_out (s (lim (taskT_im Ni) tsL) (taskT_im Ni tL))).
    refine (rf_tr2 SL _ _ o).
    + refine (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ _ _)).
      * exact (rf_trans _ _ _ (Hm _) (rf_congr (I.List_map_inst3 (ITT IN) ICT ITtt) _ _ (rf_ltT_rtL tsL))).
      * exact (rf_trans _ _ _ (rf_taskT2task_ex _) (rf_congr ITtt _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_ltT_rtL tsL) (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
  - intros t ts tsk. apply rf_ref_in.
    have o := Iref_rel _ _ _ _ _ (t (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ tsk)).
    have o' := bwS _ _ (rf_tr2 SL
      (rf_sym _ _ (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (Hm ts) (rf_taskT2task_ex tsk)))) (rf_sym _ _ (Hg ts tsk)) o).
    by rewrite rtC rtC' in o'.
Defined.

(** Function result relations, mapped pointwise: [Rnat ==> Rnat] and [Rnat ==> prod_R Rnat Rnat ==> bool_R] are handled
    by uncurrying in the builders below. *)
Definition rf_corr_lt11 (f : seq Dt.concrete_task -> Dt.concrete_task -> nat -> nat)
    (g : seq (@Rt.task_T N) -> @Rt.task_T N -> N -> N) (fL : IList ICT -> ICT -> LN -> LN) (gL : IList (ITT IN) -> ITT IN -> IN -> IN)
    (Hf : forall ts t d, Lean.eq (ne (f ts t d)) (fL (lex task_ex ts) (task_ex t) (ne d)))
    (Hg : forall ts t d, Lean.eq (Ne_ (g ts t d)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ d))) :
  TypeCorrespondence (refines (hrespectful (list_R Rt.Rtask) (hrespectful Rt.Rtask (hrespectful Rnat Rnat))) f g)
    (Iref _ _ (Ihr (IList ICT) (IList (ITT IN)) _ _ IlRt (Ihr ICT (ITT IN) _ _ IRtask (Ihr LN IN LN IN IRnat IRnat))) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros tsL tsL' rts tL tL' rt dL dL' rd.
    have o := rnat_fw _ _ (rf_ref_out s _ _ (ltR_bw _ _ rts) _ _ (rtask_bw _ _ rt) _ _ (rnat_bw _ _ rd)).
    refine (rf_tr2 IRnat _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _ _) (rf_congr3 fL _ _ _ _ _ _ (rf_lt_rtL tsL) (rf_task_rtL tL) (rf_ne_ni dL))).
    + exact (rf_trans _ _ _ (Hg _ _ _) (rf_congr3 gL _ _ _ _ _ _ (rf_ltT_rtL tsL') (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL')
        (rf_Ne_Ni dL'))).
  - intro t. apply rf_ref_in. intros ts ts' rts u u' ru d d' rd.
    have o := Iref_rel _ _ _ _ _ t _ _ (ltR_fw _ _ rts) _ _ (rtask_fw _ _ ru) _ _ (rnat_fw _ _ rd).
    apply rnat_bw'. exact (rf_tr2 IRnat (rf_sym _ _ (Hf ts u d)) (rf_sym _ _ (Hg ts' u' d')) o).
Defined.

Definition rf_corr_lt1p (f : seq Dt.concrete_task -> Dt.concrete_task -> nat -> nat * nat -> bool)
    (g : seq (@Rt.task_T N) -> @Rt.task_T N -> N -> N * N -> bool)
    (fL : IList ICT -> ICT -> LN -> IProd LN LN -> I.Bool) (gL : IList (ITT IN) -> ITT IN -> IN -> IProd IN IN -> I.Bool)
    (Hf : forall ts t R p, Lean.eq (be (f ts t R p)) (fL (lex task_ex ts) (task_ex t) (ne R) (pre ne ne p)))
    (Hg : forall ts t R p, Lean.eq (be (g ts t R p)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ R) (pre Ne_ Ne_ p))) :
  TypeCorrespondence
    (refines (hrespectful (list_R Rt.Rtask) (hrespectful Rt.Rtask (hrespectful Rnat (hrespectful pRR bool_R)))) f g)
    (Iref _ _ (Ihr (IList ICT) (IList (ITT IN)) _ _ IlRt (Ihr ICT (ITT IN) _ _ IRtask
      (Ihr LN IN _ _ IRnat (Ihr (IProd LN LN) (IProd IN IN) I.Bool I.Bool IpRR IbR)))) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros tsL tsL' rts tL tL' rt RL RL' rR pL pL' rp.
    have o := boolR_fw _ _ (rf_ref_out s _ _ (ltR_bw _ _ rts) _ _ (rtask_bw _ _ rt) _ _ (rnat_bw _ _ rR) _ _ (prr_bw _ _ rp)).
    refine (rf_tr2 IbR _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _ _ _) (rf_congr4 fL _ _ _ _ _ _ _ _ (rf_lt_rtL tsL) (rf_task_rtL tL) (rf_ne_ni RL)
        (rf_pre_pri_n pL))).
    + exact (rf_trans _ _ _ (Hg _ _ _ _) (rf_congr4 gL _ _ _ _ _ _ _ _ (rf_ltT_rtL tsL') (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL')
        (rf_Ne_Ni RL') (rf_pre_pri_N pL'))).
  - intro t. apply rf_ref_in. intros ts ts' rts u u' ru R R' rR p p' rp.
    have o := Iref_rel _ _ _ _ _ t _ _ (ltR_fw _ _ rts) _ _ (rtask_fw _ _ ru) _ _ (rnat_fw _ _ rR) _ _ (prr_fw _ _ rp).
    apply boolR_bw'. exact (rf_tr2 IbR (rf_sym _ _ (Hf ts u R p)) (rf_sym _ _ (Hg ts' u' R' p')) o).
Defined.

Definition rf_corr_TT11 (f : seq Dt.concrete_task -> Dt.concrete_task -> nat -> nat)
    (g : seq (@Rt.task_T N) -> @Rt.task_T N -> N -> N) (fL : IList ICT -> ICT -> LN -> LN) (gL : IList (ITT IN) -> ITT IN -> IN -> IN)
    (Hf : forall ts t d, Lean.eq (ne (f ts t d)) (fL (lex task_ex ts) (task_ex t) (ne d)))
    (Hg : forall ts t d, Lean.eq (Ne_ (g ts t d)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ d))) :
  TypeCorrespondence
    (forall (ts : seq (@Rt.task_T N)) (tsk : @Rt.task_T N),
       refines (hrespectful Rnat Rnat) (f (map Rt.taskT_to_task ts) (Rt.taskT_to_task tsk)) (g ts tsk))
    (forall (ts : IList (ITT IN)) (tsk : ITT IN),
       Iref _ _ (Ihr LN IN LN IN IRnat IRnat) (fL (I.List_map_inst3 (ITT IN) ICT ITtt ts) (ITtt tsk)) (gL ts tsk)).
Proof.
  have Hm := fun ts => rf_map_ex (taskT_ex Ne_) task_ex Rt.taskT_to_task ITtt rf_taskT2task_ex ts.
  split.
  - intros s tsL tL. apply Iref_mk. intros dL dL' rd.
    have o := rnat_fw _ _ (rf_ref_out (s (lim (taskT_im Ni) tsL) (taskT_im Ni tL)) _ _ (rnat_bw _ _ rd)).
    refine (rf_tr2 IRnat _ _ o).
    + refine (rf_trans _ _ _ (Hf _ _ _) (rf_congr3 fL _ _ _ _ _ _ _ _ (rf_ne_ni dL))).
      * exact (rf_trans _ _ _ (Hm _) (rf_congr (I.List_map_inst3 (ITT IN) ICT ITtt) _ _ (rf_ltT_rtL tsL))).
      * exact (rf_trans _ _ _ (rf_taskT2task_ex _) (rf_congr ITtt _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
    + exact (rf_trans _ _ _ (Hg _ _ _) (rf_congr3 gL _ _ _ _ _ _ (rf_ltT_rtL tsL) (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL)
        (rf_Ne_Ni dL'))).
  - intros t ts tsk. apply rf_ref_in. intros d d' rd.
    have o := Iref_rel _ _ _ _ _ (t (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ tsk)) _ _ (rnat_fw _ _ rd).
    apply rnat_bw'. exact (rf_tr2 IRnat
      (rf_sym _ _ (rf_trans _ _ _ (Hf _ _ _) (rf_congr3 fL _ _ _ _ _ _ (Hm ts) (rf_taskT2task_ex tsk) (rf_refl _))))
      (rf_sym _ _ (Hg ts tsk d')) o).
Defined.

Definition rf_corr_TT1p (f : seq Dt.concrete_task -> Dt.concrete_task -> nat -> nat * nat -> bool)
    (g : seq (@Rt.task_T N) -> @Rt.task_T N -> N -> N * N -> bool)
    (fL : IList ICT -> ICT -> LN -> IProd LN LN -> I.Bool) (gL : IList (ITT IN) -> ITT IN -> IN -> IProd IN IN -> I.Bool)
    (Hf : forall ts t R p, Lean.eq (be (f ts t R p)) (fL (lex task_ex ts) (task_ex t) (ne R) (pre ne ne p)))
    (Hg : forall ts t R p, Lean.eq (be (g ts t R p)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ R) (pre Ne_ Ne_ p))) :
  TypeCorrespondence
    (forall (ts : seq (@Rt.task_T N)) (tsk : @Rt.task_T N),
       refines (hrespectful Rnat (hrespectful pRR bool_R)) (f (map Rt.taskT_to_task ts) (Rt.taskT_to_task tsk)) (g ts tsk))
    (forall (ts : IList (ITT IN)) (tsk : ITT IN),
       Iref _ _ (Ihr LN IN _ _ IRnat (Ihr (IProd LN LN) (IProd IN IN) I.Bool I.Bool IpRR IbR))
         (fL (I.List_map_inst3 (ITT IN) ICT ITtt ts) (ITtt tsk)) (gL ts tsk)).
Proof.
  have Hm := fun ts => rf_map_ex (taskT_ex Ne_) task_ex Rt.taskT_to_task ITtt rf_taskT2task_ex ts.
  split.
  - intros s tsL tL. apply Iref_mk. intros RL RL' rR pL pL' rp.
    have o := boolR_fw _ _ (rf_ref_out (s (lim (taskT_im Ni) tsL) (taskT_im Ni tL)) _ _ (rnat_bw _ _ rR) _ _ (prr_bw _ _ rp)).
    refine (rf_tr2 IbR _ _ o).
    + refine (rf_trans _ _ _ (Hf _ _ _ _) (rf_congr4 fL _ _ _ _ _ _ _ _ _ _ (rf_ne_ni RL) (rf_pre_pri_n pL))).
      * exact (rf_trans _ _ _ (Hm _) (rf_congr (I.List_map_inst3 (ITT IN) ICT ITtt) _ _ (rf_ltT_rtL tsL))).
      * exact (rf_trans _ _ _ (rf_taskT2task_ex _) (rf_congr ITtt _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
    + exact (rf_trans _ _ _ (Hg _ _ _ _) (rf_congr4 gL _ _ _ _ _ _ _ _ (rf_ltT_rtL tsL) (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL)
        (rf_Ne_Ni RL') (rf_pre_pri_N pL'))).
  - intros t ts tsk. apply rf_ref_in. intros R R' rR p p' rp.
    have o := Iref_rel _ _ _ _ _ (t (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ tsk)) _ _ (rnat_fw _ _ rR) _ _ (prr_fw _ _ rp).
    apply boolR_bw'. exact (rf_tr2 IbR
      (rf_sym _ _ (rf_trans _ _ _ (Hf _ _ _ _) (rf_congr4 fL _ _ _ _ _ _ _ _ (Hm ts) (rf_taskT2task_ex tsk) (rf_refl _)
        (rf_refl _))))
      (rf_sym _ _ (Hg ts tsk R' p')) o).
Defined.

(** ** The thirteen refinement instances *)
Definition rf_src_refine_search_space_emax := ltac:(src_ty Rr.refine_search_space_emax).
Definition rf_tgt_refine_search_space_emax := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_search_space_emax).
Definition refine_search_space_emax_correspondence :
  TypeCorrespondence rf_src_refine_search_space_emax rf_tgt_refine_search_space_emax.
Proof.
  split.
  - intros s tL. apply Iref_mk. intros dL dL' rd.
    have o := lrnat_fw _ _ (rf_ref_out (s (taskT_im Ni tL)) _ _ (rnat_bw _ _ rd)).
    refine (rf_tr2 (IlR LN IN IRnat) _ _ o).
    + refine (rf_trans _ _ _ (rf_fss_ex _ _) (rf_congr2 IFss _ _ _ _ _ (rf_ne_ni dL))).
      exact (rf_trans _ _ _ (rf_taskT2task_ex _) (rf_congr ITtt _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
    + exact (rf_trans _ _ _ (rf_ssN_ex _ _) (rf_congr2 IFRssN _ _ _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL) (rf_Ne_Ni dL'))).
  - intros t tsk. apply rf_ref_in. intros d d' rd.
    have o := Iref_rel _ _ _ _ _ (t (taskT_ex Ne_ tsk)) _ _ (rnat_fw _ _ rd).
    apply lrnat_bw'. exact (rf_tr2 (IlR LN IN IRnat)
      (rf_sym _ _ (rf_trans _ _ _ (rf_fss_ex _ _) (rf_congr (fun z => IFss z (ne d)) _ _ (rf_taskT2task_ex tsk))))
      (rf_sym _ _ (rf_ssN_ex tsk d')) o).
Defined.

Definition rf_corr_tt2b := @rf_corr_t2 _ _ _ _ _ _ _ _ task_ex (taskT_ex Ne_) task_im (taskT_im Ni) be be bi bi
  Rt.Rtask IRtask bool_R IbR rtask_fw rtask_bw boolR_fw boolR_bw rf_task_rtL (rf_taskT_rtL Ne_ Ni rf_Ne_Ni) rf_bi_be rf_bi_be.

Definition rf_src_refine_hep_task := ltac:(src_ty Rr.refine_hep_task).
Definition rf_tgt_refine_hep_task := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_hep_task).
Definition refine_hep_task_correspondence : TypeCorrespondence rf_src_refine_hep_task rf_tgt_refine_hep_task :=
  rf_corr_tt2b _ _ _ _ (fun t b => rf_hep_ex t b) rf_hepT_N_ex.

Definition rf_src_refine_ohep_task := ltac:(src_ty Rr.refine_ohep_task).
Definition rf_tgt_refine_ohep_task := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_ohep_task).
Definition refine_ohep_task_correspondence : TypeCorrespondence rf_src_refine_ohep_task rf_tgt_refine_ohep_task :=
  rf_corr_tt2b _ _ _ _ rf_ohep_ex rf_ohepT_N_ex.

Definition rf_src_refine_task_eqdef := ltac:(src_ty Rr.refine_task_eqdef).
Definition rf_tgt_refine_task_eqdef := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_task_eqdef).
Definition refine_task_eqdef_correspondence : TypeCorrespondence rf_src_refine_task_eqdef rf_tgt_refine_task_eqdef :=
  rf_corr_tt2b _ _ _ _ rf_task_eqdef_ex rf_FReqT_ex.

Definition rf_src_refine_total_hep_rbf := ltac:(src_ty Rr.refine_total_hep_rbf).
Definition rf_tgt_refine_total_hep_rbf := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_total_hep_rbf).
Definition refine_total_hep_rbf_correspondence : TypeCorrespondence rf_src_refine_total_hep_rbf rf_tgt_refine_total_hep_rbf :=
  rf_corr_lt11 _ _ _ _ rf_thep_ex rf_thepT_N_ex.

Definition rf_src_refine_total_hep_rbf' := ltac:(src_ty Rr.refine_total_hep_rbf').
Definition rf_tgt_refine_total_hep_rbf' := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_total_hep_rbf').
Definition refine_total_hep_rbf'_correspondence :
  TypeCorrespondence rf_src_refine_total_hep_rbf' rf_tgt_refine_total_hep_rbf' :=
  rf_corr_TT11 _ _ _ _ rf_thep_ex rf_thepT_N_ex.

Definition rf_src_refine_total_ohep_rbf := ltac:(src_ty Rr.refine_total_ohep_rbf).
Definition rf_tgt_refine_total_ohep_rbf := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_total_ohep_rbf).
Definition refine_total_ohep_rbf_correspondence :
  TypeCorrespondence rf_src_refine_total_ohep_rbf rf_tgt_refine_total_ohep_rbf :=
  rf_corr_lt11 _ _ _ _ rf_tohep_ex rf_tohepT_N_ex.

Definition rf_src_refine_check_point := ltac:(src_ty Rr.refine_check_point).
Definition rf_tgt_refine_check_point := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_check_point).
Definition refine_check_point_correspondence : TypeCorrespondence rf_src_refine_check_point rf_tgt_refine_check_point :=
  rf_corr_lt1p _ _ _ _ rf_cpFP_ex rf_cpFPT_N_ex.

Definition rf_src_refine_check_point' := ltac:(src_ty Rr.refine_check_point').
Definition rf_tgt_refine_check_point' := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_check_point').
Definition refine_check_point'_correspondence : TypeCorrespondence rf_src_refine_check_point' rf_tgt_refine_check_point' :=
  rf_corr_TT1p _ _ _ _ rf_cpFP_ex rf_cpFPT_N_ex.

Definition rf_src_refine_blocking_bound := ltac:(src_ty Rr.refine_blocking_bound).
Definition rf_tgt_refine_blocking_bound := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_blocking_bound).
Definition refine_blocking_bound_correspondence : TypeCorrespondence rf_src_refine_blocking_bound rf_tgt_refine_blocking_bound :=
  @rf_corr_lt _ _ _ _ ne Ne_ ni Ni Rnat IRnat rnat_fw rnat_bw rf_ni_ne rf_Ni_Ne _ _ _ _ rf_bb_ex rf_bbT_N_ex.

Definition rf_src_refine_blocking_bound' := ltac:(src_ty Rr.refine_blocking_bound').
Definition rf_tgt_refine_blocking_bound' := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_blocking_bound').
Definition refine_blocking_bound'_correspondence :
  TypeCorrespondence rf_src_refine_blocking_bound' rf_tgt_refine_blocking_bound' :=
  @rf_corr_TT _ _ _ _ ne Ne_ ni Ni Rnat IRnat rnat_fw rnat_bw rf_ni_ne rf_Ni_Ne _ _ _ _ rf_bb_ex rf_bbT_N_ex.

Definition rf_src_refine_check_point_NP := ltac:(src_ty Rr.refine_check_point_NP).
Definition rf_tgt_refine_check_point_NP := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_check_point_NP).
Definition refine_check_point_NP_correspondence :
  TypeCorrespondence rf_src_refine_check_point_NP rf_tgt_refine_check_point_NP :=
  rf_corr_lt1p _ _ _ _ rf_cpNP_ex rf_cpNPT_N_ex.

Definition rf_src_refine_check_point_NP' := ltac:(src_ty Rr.refine_check_point_NP').
Definition rf_tgt_refine_check_point_NP' := ltac:(src_ty I.Prosa_Implementation_Refinements_FP_Refinements_refine_check_point_NP').
Definition refine_check_point_NP'_correspondence :
  TypeCorrespondence rf_src_refine_check_point_NP' rf_tgt_refine_check_point_NP' :=
  rf_corr_TT1p _ _ _ _ rf_cpNP_ex rf_cpNPT_N_ex.
