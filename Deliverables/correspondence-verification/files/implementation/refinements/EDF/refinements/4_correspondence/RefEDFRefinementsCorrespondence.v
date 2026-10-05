(** Correspondences for [implementation/refinements/EDF/refinements.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (unchanged).  The base
    maps and definition correspondences are those of the accepted refinements.v, arrival_bound.v, task.v,
    arrival_curve.v, arrival_curve_prefix.v, fast_search_space_computation.v and EDF/fast_search_space.v
    certificates, re-bound in [RqBase] … [RqEDFFastSearchSpace].  The components and the statement builders are those
    of the accepted FP/refinements.v certificate (restated, same proofs).  Here:
    - the six generic definitions are related for related inputs (element types by identity, task lists by the
      generic task map, operation-class instances by their field, the task equality instance by its test);
    - the definitions at the binary numbers ([iota_N], the per-task and total search spaces) and the four equality
      instances are related through the binary-number maps;
    - the generic definitions at [N] (with the [N] instances and this file's [eq_task]) are related through the
      binary-number maps;
    - the nine refinement instances are related by [TypeCorrespondence].
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.EDF.refinements.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFRefinements ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RqBase
  RqArrivalBound RqTask RqArrivalCurve RqArrivalCurvePrefix RqFastSearchSpaceComputation RqEDFFastSearchSpace.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefEDFRefinements.
Module Rq := prosa.implementation.refinements.EDF.refinements.
Module Efs := prosa.implementation.refinements.EDF.fast_search_space.
Module Rac := prosa.implementation.refinements.arrival_curve.
Module Rt := prosa.implementation.refinements.task.
Module Rab := prosa.implementation.refinements.arrival_bound.
Module Dt := prosa.implementation.definitions.task.
Module RBF := prosa.analysis.definitions.request_bound_function.

Abbreviation IERtrbf := I.Prosa_Implementation_Refinements_EDF_Refinements_total_rbf_T.
Abbreviation IERbotw := I.Prosa_Implementation_Refinements_EDF_Refinements_bound_on_total_hep_workload_T.
Abbreviation IERcpFP := I.Prosa_Implementation_Refinements_EDF_Refinements_check_point_FP_T.
Abbreviation IERbb := I.Prosa_Implementation_Refinements_EDF_Refinements_blocking_bound_NP_T.
Abbreviation IERcpNP := I.Prosa_Implementation_Refinements_EDF_Refinements_check_point_NP_T.
Abbreviation IERva := I.Prosa_Implementation_Refinements_EDF_Refinements_valid_arrivals_T.
Abbreviation IERiota := I.Prosa_Implementation_Refinements_EDF_Refinements_iota_N.
Abbreviation IERtsshN := I.Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_h_N.
Abbreviation IERtssN := I.Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_N.
Abbreviation IERssN := I.Prosa_Implementation_Refinements_EDF_Refinements_search_space_emax_EDF_N.
Abbreviation IEReqL := I.Prosa_Implementation_Refinements_EDF_Refinements_eq_listN.
Abbreviation IEReqP := I.Prosa_Implementation_Refinements_EDF_Refinements_eq_NlistNN.
Abbreviation IEReqAB := I.Prosa_Implementation_Refinements_EDF_Refinements_eq_taskab.
Abbreviation IEReqT := I.Prosa_Implementation_Refinements_EDF_Refinements_eq_task.
Abbreviation INsubI := I.Prosa_Implementation_Refinements_Refinements_sub_N.
Abbreviation ITtt := I.Prosa_Implementation_Refinements_Task_taskT_to_task.
Abbreviation ITrbf := I.Prosa_Implementation_Refinements_Task_task_rbf_T.
Abbreviation ITcma := I.Prosa_Implementation_Refinements_Task_ConcreteMaxArrivals_T.

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

Section Generic.
  Context (T : Type) (zR : zero_of T) (zL : Izero_of T) (oR : one_of T) (oL : Ione_of T) (sR : sub_of T) (sL : Isub_of T)
    (aR : add_of T) (aL : Iadd_of T) (mR : mul_of T) (mL : I.Prosa_Implementation_Refinements_Refinements_mul_of T)
    (dR : div_of T) (dL : Idiv_of T) (moR : mod_of T) (moL : Imod_of T) (lR : leq_of T) (lL : Ileq_of T)
    (ltR : lt_of T) (ltL : Ilt_of T) (eR : eq_of (@Rt.task_T T)) (eL : Ieq_of (ITT T)).
  Context (Hz : ZeroRel zR zL) (Ho : OneRel oR oL) (Hs : Op2Rel sR (Isub_op T sL)) (Ha : Op2Rel aR (Iadd_op T aL))
    (Hm : Op2Rel mR (Imul_op T mL)) (Hd : Op2Rel dR (Idiv_op T dL)) (Hmo : Op2Rel moR (Imod_op T moL))
    (Hl : BOpRel lR (Ileq_op T lL)) (Hlt : BOpRel ltR (Ilt_op T ltL)) (He : EqTRel eR eL).

  Let Ho' : Lean.eq oR (Ione_op T oL) := Ho.
  Let Hz' : Lean.eq zR (Izero_op T zL) := Hz.
  Let Hrbf t d : Lean.eq (@Rt.task_rbf_T T zR oR aR mR dR moR lR t d) (ITrbf T zL oL aL mL dL moL lL (taskT_ex idr t) d) :=
    task_rbf_T_correspondence T zR zL oR oL aR aL mR mL dR dL moR moL lR lL Hz Ho Ha Hm Hd Hmo Hl t _ d d (rf_refl _) (rf_refl _).

  Lemma rf_trbfT_ex ts d :
    Lean.eq (@Rq.total_rbf_T T zR oR aR mR dR moR lR ts d) (IERtrbf T zL oL aL mL dL moL lL (lex (taskT_ex idr) ts) d).
  Proof.
    unfold Rq.total_rbf_T. cbv zeta.
    refine (rf_trans _ _ _ (rf_foldr_ex idr idr _ (Iadd_op T aL) (fun a b => Ha a b) _ _)
      (rf_congr2 (I.List_foldr_inst3 T T (Iadd_op T aL)) _ _ _ _ Hz' _)).
    exact (rf_map_ex (taskT_ex idr) idr _ _ (fun x => Hrbf x d) ts).
  Qed.

  Lemma rf_botwT_ex ts t A d :
    Lean.eq (@Rq.bound_on_total_hep_workload_T T zR oR sR aR mR dR moR lR ltR eR ts t A d)
      (IERbotw T zL oL sL aL mL dL moL lL ltL eL (lex (taskT_ex idr) ts) (taskT_ex idr t) A d).
  Proof.
    unfold Rq.bound_on_total_hep_workload_T. cbv zeta.
    refine (rf_fmf_ex (taskT_ex idr) idr _ _ (fun a b => Ha a b) _ _ Hz _ _ _ _ _
      (fun x => rf_trans _ _ _ (rf_not_ex _) (rf_congr I.Bool_not _ _ (He x t))) ts).
    intro o. refine (rf_trans _ _ _ (Hrbf o _) (rf_congr (ITrbf T zL oL aL mL dL moL lL (taskT_ex idr o)) _ _ _)).
    refine (minn_T_correspondence T ltR ltL Hlt _ _ _ _ _ (rf_refl _)).
    refine (rf_trans _ _ _ (Hs _ _) (rf_congr (fun z => Isub_op T sL z _) _ _ _)).
    refine (rf_trans _ _ _ (Ha _ _) (rf_congr (fun z => Iadd_op T aL z _) _ _ _)).
    exact (rf_trans _ _ _ (Ha A oR) (rf_congr (Iadd_op T aL A) _ _ Ho')).
  Qed.

  Lemma rf_cpFPT_ex ts t R p :
    Lean.eq (be (@Rq.check_point_FP_T T zR oR sR aR mR dR moR lR ltR eR ts t R p))
      (IERcpFP T zL oL sL aL mL dL moL lL ltL eL (lex (taskT_ex idr) ts) (taskT_ex idr t) R (pre idr idr p)).
  Proof.
    destruct p as [a f]. unfold Rq.check_point_FP_T. cbn [fst snd].
    refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (Hl f R))).
    refine (rf_trans _ _ _ (Hl _ _) (rf_congr2 (Ileq_op T lL) _ _ _ _ _ (Ha a f))).
    refine (rf_trans _ _ _ (Ha _ _) (rf_congr2 (Iadd_op T aL) _ _ _ _ _ _)).
    - refine (rf_trans _ _ _ (Hrbf t _) (rf_congr (ITrbf T zL oL aL mL dL moL lL (taskT_ex idr t)) _ _ _)).
      exact (rf_trans _ _ _ (Ha a oR) (rf_congr (Iadd_op T aL a) _ _ Ho')).
    - exact (rf_trans _ _ _ (rf_botwT_ex ts t a _) (rf_congr (IERbotw T zL oL sL aL mL dL moL lL ltL eL _ _ a) _ _ (Ha a f))).
  Qed.

  Lemma rf_bbT_ex ts t A :
    Lean.eq (@Rq.blocking_bound_NP_T T zR oR sR aR mR dR moR lR ltR ts t A)
      (IERbb T zL oL sL aL mL dL moL lL ltL (lex (taskT_ex idr) ts) (taskT_ex idr t) A).
  Proof.
    unfold Rq.blocking_bound_NP_T. cbv zeta.
    refine (rf_fmf_ex (taskT_ex idr) idr _ _ (fun a b => maxn_T_correspondence T ltR ltL Hlt a a b b (rf_refl _) (rf_refl _))
      _ _ Hz _ _ _ _ _ _ ts).
    - intro x. exact (rf_trans _ _ _ (Hs _ _) (rf_congr (Isub_op T sL _) _ _ Ho')).
    - intro x. refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
      + refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
        * refine (rf_trans _ _ _ (Hlt _ _) (rf_congr2 (Ilt_op T ltL) _ _ _ _ Hz' _)).
          exact (ConcreteMaxArrivals_T_correspondence T zR zL oR oL aR aL mR mL dR dL moR moL lR lL Hz Ho Ha Hm Hd Hmo Hl
            x _ _ _ (rf_refl _) Ho').
        * exact (rf_trans _ _ _ (Hlt _ _) (rf_congr (fun z => Ilt_op T ltL z _) _ _ Hz')).
      + exact (rf_trans _ _ _ (Hlt _ _) (rf_congr (fun z => Ilt_op T ltL z _) _ _ (Ha _ _))).
  Qed.

  Lemma rf_cpNPT_ex ts t R p :
    Lean.eq (be (@Rq.check_point_NP_T T zR oR sR aR mR dR moR lR ltR eR ts t R p))
      (IERcpNP T zL oL sL aL mL dL moL lL ltL eL (lex (taskT_ex idr) ts) (taskT_ex idr t) R (pre idr idr p)).
  Proof.
    destruct p as [a f]. unfold Rq.check_point_NP_T. cbn [fst snd].
    have Hc : Lean.eq (sR (Rt.task_cost_T t) oR) (Isub_op T sL (Rt.task_cost_T t) (Ione_op T oL)) :=
      rf_trans _ _ _ (Hs _ _) (rf_congr (Isub_op T sL _) _ _ Ho').
    refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
    - refine (rf_trans _ _ _ (Hl _ _) (rf_congr2 (Ileq_op T lL) _ _ _ _ _ (Ha a f))).
      refine (rf_trans _ _ _ (Ha _ _) (rf_congr2 (Iadd_op T aL) _ _ _ _ _ _)).
      + refine (rf_trans _ _ _ (Ha _ _) (rf_congr2 (Iadd_op T aL) _ _ _ _ (rf_bbT_ex ts t a) _)).
        refine (rf_trans _ _ _ (Hs _ _) (rf_congr2 (Isub_op T sL) _ _ _ _ _ Hc)).
        refine (rf_trans _ _ _ (Hrbf t _) (rf_congr (ITrbf T zL oL aL mL dL moL lL (taskT_ex idr t)) _ _ _)).
        exact (rf_trans _ _ _ (Ha a oR) (rf_congr (Iadd_op T aL a) _ _ Ho')).
      + exact (rf_trans _ _ _ (rf_botwT_ex ts t a _) (rf_congr (IERbotw T zL oL sL aL mL dL moL lL ltL eL _ _ a) _ _ (Ha a f))).
    - refine (rf_trans _ _ _ (Hl _ _) (rf_congr (fun z => Ileq_op T lL z R) _ _ _)).
      exact (rf_trans _ _ _ (Ha _ _) (rf_congr (Iadd_op T aL f) _ _ Hc)).
  Qed.
End Generic.

Lemma total_rbf_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL
    (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) ->
  forall tsR tsL dR' dL', Lean.eq (lex (taskT_ex idr) tsR) tsL -> Lean.eq dR' dL' ->
  Lean.eq (@Rq.total_rbf_T T zR oR aR mR dR moR lR tsR dR') (IERtrbf T zL oL aL mL dL moL lL tsL dL').
Proof.
  intros Hz Ho Ha Hm Hd Hmo Hl tsR tsL dR' dL' Hs Hd'. destruct Hs. destruct Hd'.
  eapply rf_trbfT_ex; eassumption.
Qed.

Lemma bound_on_total_hep_workload_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (sR : sub_of T) sL
    (aR : add_of T) aL (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL
    (ltR : lt_of T) ltL (eR : eq_of (@Rt.task_T T)) eL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel sR (Isub_op T sL) -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) ->
  Op2Rel dR (Idiv_op T dL) -> Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> BOpRel ltR (Ilt_op T ltL) ->
  EqTRel eR eL ->
  forall tsR tsL tR tL AR AL dR' dL', Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq AR AL ->
  Lean.eq dR' dL' ->
  Lean.eq (@Rq.bound_on_total_hep_workload_T T zR oR sR aR mR dR moR lR ltR eR tsR tR AR dR')
    (IERbotw T zL oL sL aL mL dL moL lL ltL eL tsL tL AL dL').
Proof.
  intros Hz Ho Hs Ha Hm Hd Hmo Hl Hlt He tsR tsL tR tL AR AL dR' dL' Hts Ht HA Hd'.
  destruct Hts. destruct Ht. destruct HA. destruct Hd'.
  eapply rf_botwT_ex; eassumption.
Qed.

Lemma check_point_FP_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (sR : sub_of T) sL
    (aR : add_of T) aL (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL
    (ltR : lt_of T) ltL (eR : eq_of (@Rt.task_T T)) eL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel sR (Isub_op T sL) -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) ->
  Op2Rel dR (Idiv_op T dL) -> Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> BOpRel ltR (Ilt_op T ltL) ->
  EqTRel eR eL ->
  forall tsR tsL tR tL RR RL pR pL, Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq RR RL ->
  Lean.eq (pre idr idr pR) pL ->
  Lean.eq (be (@Rq.check_point_FP_T T zR oR sR aR mR dR moR lR ltR eR tsR tR RR pR))
    (IERcpFP T zL oL sL aL mL dL moL lL ltL eL tsL tL RL pL).
Proof.
  intros Hz Ho Hs Ha Hm Hd Hmo Hl Hlt He tsR tsL tR tL RR RL pR pL Hts Ht HR Hp.
  destruct Hts. destruct Ht. destruct HR. destruct Hp.
  eapply rf_cpFPT_ex; eassumption.
Qed.

Lemma blocking_bound_NP_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (sR : sub_of T) sL
    (aR : add_of T) aL (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL
    (ltR : lt_of T) ltL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel sR (Isub_op T sL) -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) ->
  Op2Rel dR (Idiv_op T dL) -> Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> BOpRel ltR (Ilt_op T ltL) ->
  forall tsR tsL tR tL AR AL, Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq AR AL ->
  Lean.eq (@Rq.blocking_bound_NP_T T zR oR sR aR mR dR moR lR ltR tsR tR AR)
    (IERbb T zL oL sL aL mL dL moL lL ltL tsL tL AL).
Proof.
  intros Hz Ho Hs Ha Hm Hd Hmo Hl Hlt tsR tsL tR tL AR AL Hts Ht HA. destruct Hts. destruct Ht. destruct HA.
  eapply rf_bbT_ex; eassumption.
Qed.

Lemma check_point_NP_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (sR : sub_of T) sL
    (aR : add_of T) aL (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL
    (ltR : lt_of T) ltL (eR : eq_of (@Rt.task_T T)) eL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel sR (Isub_op T sL) -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) ->
  Op2Rel dR (Idiv_op T dL) -> Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> BOpRel ltR (Ilt_op T ltL) ->
  EqTRel eR eL ->
  forall tsR tsL tR tL RR RL pR pL, Lean.eq (lex (taskT_ex idr) tsR) tsL -> TaskTRel tR tL -> Lean.eq RR RL ->
  Lean.eq (pre idr idr pR) pL ->
  Lean.eq (be (@Rq.check_point_NP_T T zR oR sR aR mR dR moR lR ltR eR tsR tR RR pR))
    (IERcpNP T zL oL sL aL mL dL moL lL ltL eL tsL tL RL pL).
Proof.
  intros Hz Ho Hs Ha Hm Hd Hmo Hl Hlt He tsR tsL tR tL RR RL pR pL Hts Ht HR Hp.
  destruct Hts. destruct Ht. destruct HR. destruct Hp.
  eapply rf_cpNPT_ex; eassumption.
Qed.

Lemma valid_arrivals_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (eR : eq_of T) eL
    (lR : leq_of T) lL (tR' : lt_of T) tL' :
  ZeroRel zR zL -> OneRel oR oL -> BOpRel eR (Ieq_op T eL) -> BOpRel lR (Ileq_op T lL) -> BOpRel tR' (Ilt_op T tL') ->
  forall tR tL, TaskTRel tR tL ->
  Lean.eq (be (@Rq.valid_arrivals_T T zR oR eR lR tR' tR)) (IERva T zL oL eL lL tL' tL).
Proof.
  intros Hz Ho He Hl Ht tR tL H. destruct H. have Ho' : Lean.eq oR (Ione_op T oL) := Ho.
  destruct tR as [i c a d p]. unfold Rq.valid_arrivals_T. cbn.
  destruct a as [x|x|e]; cbn [tabT_ex].
  - exact (rf_trans _ _ _ (Hl oR x) (rf_congr (fun z => Ileq_op T lL z x) _ _ Ho')).
  - exact (rf_trans _ _ _ (Hl oR x) (rf_congr (fun z => Ileq_op T lL z x) _ _ Ho')).
  - exact (valid_extrapolated_arrival_curve_T_correspondence T zR zL oR oL eR eL lR lL tR' tL' Hz Ho He Hl Ht e _ (rf_refl _)).
Qed.

(** ** The equality instances *)
Lemma rf_EReqL_ex x y : Lean.eq (be (Rq.eq_listN x y)) (Ieq_op (IList IN) IEReqL (lex Ne_ x) (lex Ne_ y)).
Proof. exact (rf_decide_ex _ _ _ (rf_eqtype_rel (lex Ne_) (lim Ni) (rf_lim_lex Ne_ Ni rf_Ni_Ne) x y)). Qed.

Lemma eq_listN_correspondence xR xL yR yL :
  Lean.eq (lex Ne_ xR) xL -> Lean.eq (lex Ne_ yR) yL -> Lean.eq (be (Rq.eq_listN xR yR)) (Ieq_op (IList IN) IEReqL xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_EReqL_ex xR yR). Qed.

Lemma rf_EReqP_ex x y :
  Lean.eq (be (Rq.eq_NlistNN x y)) (Ieq_op (IProd IN (IList (IProd IN IN))) IEReqP (pfx Ne_ x) (pfx Ne_ y)).
Proof. exact (rf_eq_NlistNN_ex x y). Qed.

Lemma eq_NlistNN_correspondence xR xL yR yL :
  Lean.eq (pfx Ne_ xR) xL -> Lean.eq (pfx Ne_ yR) yL ->
  Lean.eq (be (Rq.eq_NlistNN xR yR)) (Ieq_op (IProd IN (IList (IProd IN IN))) IEReqP xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_EReqP_ex xR yR). Qed.

Lemma rf_EReqAB_ex x y : Lean.eq (be (Rq.eq_taskab x y)) (Ieq_op (ITab IN) IEReqAB (tabT_ex Ne_ x) (tabT_ex Ne_ y)).
Proof. exact (rf_eq_taskab_ex x y). Qed.

Lemma eq_taskab_correspondence xR xL yR yL :
  Lean.eq (tabT_ex Ne_ xR) xL -> Lean.eq (tabT_ex Ne_ yR) yL ->
  Lean.eq (be (Rq.eq_taskab xR yR)) (Ieq_op (ITab IN) IEReqAB xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_EReqAB_ex xR yR). Qed.

Lemma rf_EReqT_ex x y : Lean.eq (be (Rq.eq_task x y)) (Ieq_op (ITT IN) IEReqT (taskT_ex Ne_ x) (taskT_ex Ne_ y)).
Proof.
  destruct x as [i1 c1 a1 d1 p1]; destruct y as [i2 c2 a2 d2 p2].
  change (Lean.eq (be (Rt.task_eqdef_T (Rt.Build_task_T i1 c1 a1 d1 p1) (Rt.Build_task_T i2 c2 a2 d2 p2)))
    (Ieq_op (ITT IN) IEReqT (taskT_ex Ne_ (Rt.Build_task_T i1 c1 a1 d1 p1)) (taskT_ex Ne_ (Rt.Build_task_T i2 c2 a2 d2 p2)))).
  unfold Rt.task_eqdef_T. cbn.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_N_eqb_ex p1 p2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_N_eqb_ex d1 d2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_EReqAB_ex a1 a2))).
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_N_eqb_ex i1 i2) (rf_N_eqb_ex c1 c2))).
Qed.

Lemma eq_task_correspondence xR xL yR yL :
  Lean.eq (taskT_ex Ne_ xR) xL -> Lean.eq (taskT_ex Ne_ yR) yL ->
  Lean.eq (be (Rq.eq_task xR yR)) (Ieq_op (ITT IN) IEReqT xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_EReqT_ex xR yR). Qed.

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


(** ** Definitions at the binary numbers *)
Lemma rf_iotaN_ex a d : Lean.eq (lex Ne_ (Rq.iota_N a d)) (IERiota (Ne_ a) (Ne_ d)).
Proof.
  exact (rf_trans _ _ _ (rf_iota_T_N_ex a (nat_of_bin d))
    (rf_congr (I.Prosa_Implementation_Refinements_Refinements_iota_T IN IN1 INaddI (Ne_ a)) _ _ (rf_nat_of_bin_ex d))).
Qed.

Lemma iota_N_correspondence aR aL dR dL :
  Lean.eq (Ne_ aR) aL -> Lean.eq (Ne_ dR) dL -> Lean.eq (lex Ne_ (Rq.iota_N aR dR)) (IERiota aL dL).
Proof. intros Ha Hd. destruct Ha. destruct Hd. exact (rf_iotaN_ex aR dR). Qed.

Lemma rf_tsshN_ex t o l r :
  Lean.eq (lex Ne_ (Rq.task_search_space_emax_EDF_h_N t o l r)) (IERtsshN (taskT_ex Ne_ t) (taskT_ex Ne_ o) (Ne_ l) (Ne_ r)).
Proof.
  unfold Rq.task_search_space_emax_EDF_h_N. cbv zeta.
  refine (rf_trans _ _ _ (rf_map_ex Ne_ Ne_ _ _ rf_predn_T_N_ex _) (rf_congr (I.List_map_inst3 IN IN _) _ _ _)).
  refine (rf_trans _ _ _ (rf_spn_T_N_ex _ _) (rf_congr (fun l => I.Prosa_Implementation_Refinements_Refinements_shift_points_neg_T
    IN INsubI INleqI l _) _ _ _)).
  refine (rf_trans _ _ _ (rf_spp_T_N_ex _ _) (rf_congr (fun l => I.Prosa_Implementation_Refinements_Refinements_shift_points_pos_T
    IN INaddI l _) _ _ _)).
  refine (rf_trans _ _ _ (rf_rswoT_N_ex o _) (rf_congr (I.Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T IN
    IN1 INaddI (taskT_ex Ne_ o)) _ _ _)).
  exact (rf_trans _ _ _ (rf_map_ex Ne_ Ne_ _ (INmul (I.Prosa_Implementation_Refinements_Task_get_horizon_of_task_T IN IN1
    (taskT_ex Ne_ o))) (fun i => rf_trans _ _ _ (rf_N_mul_ex _ i) (rf_congr (fun h => INmul h (Ne_ i)) _ _ (rf_ghotT_N_ex o))) _)
    (rf_congr (I.List_map_inst3 IN IN _) _ _ (rf_iotaN_ex l r))).
Qed.

Lemma task_search_space_emax_EDF_h_N_correspondence tR tL oR oL lR lL rR rL :
  Lean.eq (taskT_ex Ne_ tR) tL -> Lean.eq (taskT_ex Ne_ oR) oL -> Lean.eq (Ne_ lR) lL -> Lean.eq (Ne_ rR) rL ->
  Lean.eq (lex Ne_ (Rq.task_search_space_emax_EDF_h_N tR oR lR rR)) (IERtsshN tL oL lL rL).
Proof. intros Ht Ho Hl Hr. destruct Ht. destruct Ho. destruct Hl. destruct Hr. exact (rf_tsshN_ex tR oR lR rR). Qed.

Lemma rf_tssN_ex t o L :
  Lean.eq (lex Ne_ (Rq.task_search_space_emax_EDF_N t o L)) (IERtssN (taskT_ex Ne_ t) (taskT_ex Ne_ o) (Ne_ L)).
Proof.
  unfold Rq.task_search_space_emax_EDF_N. cbv zeta.
  refine (rf_trans _ _ _ (rf_tsshN_ex t o _ _) (rf_congr (IERtsshN (taskT_ex Ne_ t) (taskT_ex Ne_ o) (Ne_ N0)) _ _ _)).
  refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr (fun z => INadd z (Ne_ (Npos xH))) _ _ _)).
  refine (rf_trans _ _ _ (rf_N_div_ex _ _) (rf_congr2 INdiv _ _ _ _ _ (rf_ghotT_N_ex o))).
  exact (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr (INadd (Ne_ L)) _ _ (rf_N_sub_ex _ _))).
Qed.

Lemma task_search_space_emax_EDF_N_correspondence tR tL oR oL LR LL :
  Lean.eq (taskT_ex Ne_ tR) tL -> Lean.eq (taskT_ex Ne_ oR) oL -> Lean.eq (Ne_ LR) LL ->
  Lean.eq (lex Ne_ (Rq.task_search_space_emax_EDF_N tR oR LR)) (IERtssN tL oL LL).
Proof. intros Ht Ho HL. destruct Ht. destruct Ho. destruct HL. exact (rf_tssN_ex tR oR LR). Qed.

Lemma rf_ssEN_ex ts t L :
  Lean.eq (lex Ne_ (Rq.search_space_emax_EDF_N ts t L)) (IERssN (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ L)).
Proof.
  unfold Rq.search_space_emax_EDF_N. cbv zeta.
  refine (rf_trans _ _ _ (rf_flatten_ex Ne_ _) (rf_congr (I.List_flatten_inst1 IN) _ _ _)).
  exact (rf_map_ex (taskT_ex Ne_) (lex Ne_) _ _ (fun o => rf_tssN_ex t o L) ts).
Qed.

Lemma search_space_emax_EDF_N_correspondence tsR tsL tR tL LR LL :
  Lean.eq (lex (taskT_ex Ne_) tsR) tsL -> Lean.eq (taskT_ex Ne_ tR) tL -> Lean.eq (Ne_ LR) LL ->
  Lean.eq (lex Ne_ (Rq.search_space_emax_EDF_N tsR tR LR)) (IERssN tsL tL LL).
Proof. intros Hs Ht HL. destruct Hs. destruct Ht. destruct HL. exact (rf_ssEN_ex tsR tR LR). Qed.

(** ** The generic definitions at [N] (with the [N] instances and this file's [eq_task]) *)
Lemma rf_trbfT_N_ex ts d :
  Lean.eq (Ne_ (Rq.total_rbf_T ts d)) (IERtrbf IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI (lex (taskT_ex Ne_) ts) (Ne_ d)).
Proof.
  unfold Rq.total_rbf_T. cbv zeta.
  refine (rf_trans _ _ _ (rf_foldr_ex Ne_ Ne_ _ _ rf_N_add_ex _ _) (rf_congr2 (I.List_foldr_inst3 IN IN _) _ _ _ _ (rf_refl _) _)).
  exact (rf_map_ex (taskT_ex Ne_) Ne_ _ _ (fun x => rf_rbfT_N_ex x d) ts).
Qed.

Lemma rf_botwT_N_ex ts t A d :
  Lean.eq (Ne_ (Rq.bound_on_total_hep_workload_T ts t A d))
    (IERbotw IN IN0 IN1 INsubI INaddI INmulI INdivI INmodI INleqI INltI IEReqT (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t)
       (Ne_ A) (Ne_ d)).
Proof.
  unfold Rq.bound_on_total_hep_workload_T. cbv zeta.
  refine (rf_fmf_ex (taskT_ex Ne_) Ne_ _ _ rf_N_add_ex _ _ (rf_refl _) _ _ _ _ _
    (fun x => rf_trans _ _ _ (rf_not_ex _) (rf_congr I.Bool_not _ _ (rf_EReqT_ex x t))) ts).
  intro o. refine (rf_trans _ _ _ (rf_rbfT_N_ex o _) (rf_congr (ITrbf IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI
    (taskT_ex Ne_ o)) _ _ _)).
  refine (rf_trans _ _ _ (rf_minn_T_N_ex _ _) (rf_congr (fun z => I.Prosa_Implementation_Refinements_Refinements_minn_T IN INltI
    z (Ne_ d)) _ _ _)).
  refine (rf_trans _ _ _ (rf_N_sub_ex _ _) (rf_congr (fun z => INsub z _) _ _ _)).
  exact (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr (fun z => INadd z _) _ _ (rf_N_add_ex A (Npos xH)))).
Qed.

Lemma rf_cpFPT_N_ex ts t R p :
  Lean.eq (be (Rq.check_point_FP_T ts t R p))
    (IERcpFP IN IN0 IN1 INsubI INaddI INmulI INdivI INmodI INleqI INltI IEReqT (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t)
       (Ne_ R) (pre Ne_ Ne_ p)).
Proof.
  destruct p as [a f]. unfold Rq.check_point_FP_T. cbn [fst snd].
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_N_leb_ex f R))).
  refine (rf_trans _ _ _ (rf_N_leb_ex _ _) (rf_congr2 INleb _ _ _ _ _ (rf_N_add_ex a f))).
  refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr2 INadd _ _ _ _ _ _)).
  - exact (rf_trans _ _ _ (rf_rbfT_N_ex t _) (rf_congr (ITrbf IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI (taskT_ex Ne_ t))
      _ _ (rf_N_add_ex a (Npos xH)))).
  - exact (rf_trans _ _ _ (rf_botwT_N_ex ts t a _) (rf_congr (IERbotw IN IN0 IN1 INsubI INaddI INmulI INdivI INmodI INleqI
      INltI IEReqT _ _ (Ne_ a)) _ _ (rf_N_add_ex a f))).
Qed.

Lemma rf_bbT_N_ex ts t A :
  Lean.eq (Ne_ (Rq.blocking_bound_NP_T ts t A))
    (IERbb IN IN0 IN1 INsubI INaddI INmulI INdivI INmodI INleqI INltI (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ A)).
Proof.
  unfold Rq.blocking_bound_NP_T. cbv zeta.
  refine (rf_fmf_ex (taskT_ex Ne_) Ne_ _ _ rf_maxn_T_N_ex _ _ (rf_refl _) _ _ _ _ _ _ ts).
  - intro x. exact (rf_N_sub_ex _ _).
  - intro x. refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
    + refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_N_ltb_ex _ _))).
      exact (rf_trans _ _ _ (rf_N_ltb_ex _ _) (rf_congr (INltb (Ne_ N0)) _ _ (rf_cmaT_N_ex x _))).
    + exact (rf_trans _ _ _ (rf_N_ltb_ex _ _) (rf_congr (fun z => INltb z _) _ _ (rf_N_add_ex _ _))).
Qed.

Lemma rf_cpNPT_N_ex ts t R p :
  Lean.eq (be (Rq.check_point_NP_T ts t R p))
    (IERcpNP IN IN0 IN1 INsubI INaddI INmulI INdivI INmodI INleqI INltI IEReqT (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t)
       (Ne_ R) (pre Ne_ Ne_ p)).
Proof.
  destruct p as [a f]. unfold Rq.check_point_NP_T. cbn [fst snd].
  have Hc := rf_N_sub_ex (Rt.task_cost_T t) (Npos xH).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
  - refine (rf_trans _ _ _ (rf_N_leb_ex _ _) (rf_congr2 INleb _ _ _ _ _ (rf_N_add_ex a f))).
    refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr2 INadd _ _ _ _ _ _)).
    + refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr2 INadd _ _ _ _ (rf_bbT_N_ex ts t a) _)).
      refine (rf_trans _ _ _ (rf_N_sub_ex _ _) (rf_congr2 INsub _ _ _ _ _ Hc)).
      exact (rf_trans _ _ _ (rf_rbfT_N_ex t _) (rf_congr (ITrbf IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI (taskT_ex Ne_ t))
        _ _ (rf_N_add_ex a (Npos xH)))).
    + exact (rf_trans _ _ _ (rf_botwT_N_ex ts t a _) (rf_congr (IERbotw IN IN0 IN1 INsubI INaddI INmulI INdivI INmodI INleqI
        INltI IEReqT _ _ (Ne_ a)) _ _ (rf_N_add_ex a f))).
  - refine (rf_trans _ _ _ (rf_N_leb_ex _ _) (rf_congr (fun z => INleb z (Ne_ R)) _ _ _)).
    exact (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr (INadd (Ne_ f)) _ _ Hc)).
Qed.

(** ** The natural-number total request-bound function *)
Lemma rf_sumSeqE_ex {X Y : Type} (e : X -> Y) (F : X -> nat) (FL : Y -> LN) (HF : forall x, Lean.eq (ne (F x)) (FL (e x))) xs :
  Lean.eq (ne (\sum_(x <- xs) F x)) (I.Prosa_Util_Sum_sumSeq_inst1 Y (lex e xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil. exact (rf_refl _).
  - rewrite big_cons.
    exact (rf_trans _ _ _ (rf_add_ex _ _) (rf_congr2 sub_imported_add _ _ _ _ (HF x) IH)).
Qed.

Lemma rf_trbf_ex ts d :
  Lean.eq (ne (RBF.total_request_bound_function ts d))
    (I.Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function_inst1 ITask
       I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task I.Prosa_Implementation_Definitions_Task_TaskCost
       I.Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals (lex task_ex ts) (ne d)).
Proof.
  unfold RBF.total_request_bound_function.
  exact (rf_sumSeqE_ex task_ex _ (fun y => IAC_task_rbf y (ne d)) (fun o => task_rbf_correspondence o _ d _ (rf_refl _) (rf_refl _)) ts).
Qed.

(** ** More builders *)
Definition rf_corr_lt111 (f : seq Dt.concrete_task -> Dt.concrete_task -> nat -> nat -> nat)
    (g : seq (@Rt.task_T N) -> @Rt.task_T N -> N -> N -> N)
    (fL : IList ICT -> ICT -> LN -> LN -> LN) (gL : IList (ITT IN) -> ITT IN -> IN -> IN -> IN)
    (Hf : forall ts t a d, Lean.eq (ne (f ts t a d)) (fL (lex task_ex ts) (task_ex t) (ne a) (ne d)))
    (Hg : forall ts t a d, Lean.eq (Ne_ (g ts t a d)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ a) (Ne_ d))) :
  TypeCorrespondence
    (refines (hrespectful (list_R Rt.Rtask) (hrespectful Rt.Rtask (hrespectful Rnat (hrespectful Rnat Rnat)))) f g)
    (Iref _ _ (Ihr (IList ICT) (IList (ITT IN)) _ _ IlRt (Ihr ICT (ITT IN) _ _ IRtask
      (Ihr LN IN _ _ IRnat (Ihr LN IN LN IN IRnat IRnat)))) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros tsL tsL' rts tL tL' rt aL aL' ra dL dL' rd.
    have o := rnat_fw _ _ (rf_ref_out s _ _ (ltR_bw _ _ rts) _ _ (rtask_bw _ _ rt) _ _ (rnat_bw _ _ ra) _ _ (rnat_bw _ _ rd)).
    refine (rf_tr2 IRnat _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _ _ _) (rf_congr4 fL _ _ _ _ _ _ _ _ (rf_lt_rtL tsL) (rf_task_rtL tL) (rf_ne_ni aL)
        (rf_ne_ni dL))).
    + exact (rf_trans _ _ _ (Hg _ _ _ _) (rf_congr4 gL _ _ _ _ _ _ _ _ (rf_ltT_rtL tsL') (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL')
        (rf_Ne_Ni aL') (rf_Ne_Ni dL'))).
  - intro t. apply rf_ref_in. intros ts ts' rts u u' ru a a' ra d d' rd.
    have o := Iref_rel _ _ _ _ _ t _ _ (ltR_fw _ _ rts) _ _ (rtask_fw _ _ ru) _ _ (rnat_fw _ _ ra) _ _ (rnat_fw _ _ rd).
    apply rnat_bw'. exact (rf_tr2 IRnat (rf_sym _ _ (Hf ts u a d)) (rf_sym _ _ (Hg ts' u' a' d')) o).
Defined.

Definition rf_corr_TT1l (f : seq Dt.concrete_task -> Dt.concrete_task -> nat -> seq nat)
    (g : seq (@Rt.task_T N) -> @Rt.task_T N -> N -> seq N)
    (fL : IList ICT -> ICT -> LN -> IList LN) (gL : IList (ITT IN) -> ITT IN -> IN -> IList IN)
    (Hf : forall ts t d, Lean.eq (lex ne (f ts t d)) (fL (lex task_ex ts) (task_ex t) (ne d)))
    (Hg : forall ts t d, Lean.eq (lex Ne_ (g ts t d)) (gL (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ t) (Ne_ d))) :
  TypeCorrespondence
    (forall (ts : seq (@Rt.task_T N)) (tsk : @Rt.task_T N),
       refines (hrespectful Rnat (list_R Rnat)) (f (map Rt.taskT_to_task ts) (Rt.taskT_to_task tsk)) (g ts tsk))
    (forall (ts : IList (ITT IN)) (tsk : ITT IN),
       Iref _ _ (Ihr LN IN _ _ IRnat (IlR LN IN IRnat)) (fL (I.List_map_inst3 (ITT IN) ICT ITtt ts) (ITtt tsk)) (gL ts tsk)).
Proof.
  have Hm := fun ts => rf_map_ex (taskT_ex Ne_) task_ex Rt.taskT_to_task ITtt rf_taskT2task_ex ts.
  split.
  - intros s tsL tL. apply Iref_mk. intros dL dL' rd.
    have o := lrnat_fw _ _ (rf_ref_out (s (lim (taskT_im Ni) tsL) (taskT_im Ni tL)) _ _ (rnat_bw _ _ rd)).
    refine (rf_tr2 (IlR LN IN IRnat) _ _ o).
    + refine (rf_trans _ _ _ (Hf _ _ _) (rf_congr3 fL _ _ _ _ _ _ _ _ (rf_ne_ni dL))).
      * exact (rf_trans _ _ _ (Hm _) (rf_congr (I.List_map_inst3 (ITT IN) ICT ITtt) _ _ (rf_ltT_rtL tsL))).
      * exact (rf_trans _ _ _ (rf_taskT2task_ex _) (rf_congr ITtt _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
    + exact (rf_trans _ _ _ (Hg _ _ _) (rf_congr3 gL _ _ _ _ _ _ (rf_ltT_rtL tsL) (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL)
        (rf_Ne_Ni dL'))).
  - intros t ts tsk. apply rf_ref_in. intros d d' rd.
    have o := Iref_rel _ _ _ _ _ (t (lex (taskT_ex Ne_) ts) (taskT_ex Ne_ tsk)) _ _ (rnat_fw _ _ rd).
    apply lrnat_bw'. exact (rf_tr2 (IlR LN IN IRnat)
      (rf_sym _ _ (rf_trans _ _ _ (Hf _ _ _) (rf_congr3 fL _ _ _ _ _ _ (Hm ts) (rf_taskT2task_ex tsk) (rf_refl _))))
      (rf_sym _ _ (Hg ts tsk d')) o).
Defined.

Definition rf_corr_T21l (f : Dt.concrete_task -> Dt.concrete_task -> nat -> seq nat)
    (g : @Rt.task_T N -> @Rt.task_T N -> N -> seq N)
    (fL : ICT -> ICT -> LN -> IList LN) (gL : ITT IN -> ITT IN -> IN -> IList IN)
    (Hf : forall t o d, Lean.eq (lex ne (f t o d)) (fL (task_ex t) (task_ex o) (ne d)))
    (Hg : forall t o d, Lean.eq (lex Ne_ (g t o d)) (gL (taskT_ex Ne_ t) (taskT_ex Ne_ o) (Ne_ d))) :
  TypeCorrespondence
    (forall tsk tsko : @Rt.task_T N,
       refines (hrespectful Rnat (list_R Rnat)) (f (Rt.taskT_to_task tsk) (Rt.taskT_to_task tsko)) (g tsk tsko))
    (forall tsk tsko : ITT IN, Iref _ _ (Ihr LN IN _ _ IRnat (IlR LN IN IRnat)) (fL (ITtt tsk) (ITtt tsko)) (gL tsk tsko)).
Proof.
  have Hc := fun tL => rf_trans _ _ _ (rf_taskT2task_ex _) (rf_congr ITtt _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL)).
  split.
  - intros s tL oL. apply Iref_mk. intros dL dL' rd.
    have o := lrnat_fw _ _ (rf_ref_out (s (taskT_im Ni tL) (taskT_im Ni oL)) _ _ (rnat_bw _ _ rd)).
    refine (rf_tr2 (IlR LN IN IRnat) _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _ _) (rf_congr3 fL _ _ _ _ _ _ (Hc tL) (Hc oL) (rf_ne_ni dL))).
    + exact (rf_trans _ _ _ (Hg _ _ _) (rf_congr3 gL _ _ _ _ _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL)
        (rf_taskT_rtL Ne_ Ni rf_Ne_Ni oL) (rf_Ne_Ni dL'))).
  - intros t tsk tsko. apply rf_ref_in. intros d d' rd.
    have o := Iref_rel _ _ _ _ _ (t (taskT_ex Ne_ tsk) (taskT_ex Ne_ tsko)) _ _ (rnat_fw _ _ rd).
    apply lrnat_bw'. exact (rf_tr2 (IlR LN IN IRnat)
      (rf_sym _ _ (rf_trans _ _ _ (Hf _ _ _) (rf_congr3 fL _ _ _ _ _ _ (rf_taskT2task_ex tsk) (rf_taskT2task_ex tsko)
        (rf_refl _)))) (rf_sym _ _ (Hg tsk tsko d')) o).
Defined.

Definition rf_corr_TS11 (f : seq Dt.concrete_task -> nat -> nat) (g : seq (@Rt.task_T N) -> N -> N)
    (fL : IList ICT -> LN -> LN) (gL : IList (ITT IN) -> IN -> IN)
    (Hf : forall ts d, Lean.eq (ne (f ts d)) (fL (lex task_ex ts) (ne d)))
    (Hg : forall ts d, Lean.eq (Ne_ (g ts d)) (gL (lex (taskT_ex Ne_) ts) (Ne_ d))) :
  TypeCorrespondence
    (forall ts : seq (@Rt.task_T N), refines (hrespectful Rnat Rnat) (f (map Rt.taskT_to_task ts)) (g ts))
    (forall ts : IList (ITT IN), Iref _ _ (Ihr LN IN LN IN IRnat IRnat) (fL (I.List_map_inst3 (ITT IN) ICT ITtt ts)) (gL ts)).
Proof.
  have Hm := fun ts => rf_map_ex (taskT_ex Ne_) task_ex Rt.taskT_to_task ITtt rf_taskT2task_ex ts.
  split.
  - intros s tsL. apply Iref_mk. intros dL dL' rd.
    have o := rnat_fw _ _ (rf_ref_out (s (lim (taskT_im Ni) tsL)) _ _ (rnat_bw _ _ rd)).
    refine (rf_tr2 IRnat _ _ o).
    + refine (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ _ (rf_ne_ni dL))).
      exact (rf_trans _ _ _ (Hm _) (rf_congr (I.List_map_inst3 (ITT IN) ICT ITtt) _ _ (rf_ltT_rtL tsL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_ltT_rtL tsL) (rf_Ne_Ni dL'))).
  - intros t ts. apply rf_ref_in. intros d d' rd.
    have o := Iref_rel _ _ _ _ _ (t (lex (taskT_ex Ne_) ts)) _ _ (rnat_fw _ _ rd).
    apply rnat_bw'. exact (rf_tr2 IRnat
      (rf_sym _ _ (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (Hm ts) (rf_refl _)))) (rf_sym _ _ (Hg ts d')) o).
Defined.

(** ** The nine refinement instances *)
Definition rf_src_refine_blocking_bound := ltac:(src_ty Rq.refine_blocking_bound).
Definition rf_tgt_refine_blocking_bound := ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_blocking_bound).
Definition refine_blocking_bound_correspondence : TypeCorrespondence rf_src_refine_blocking_bound rf_tgt_refine_blocking_bound :=
  rf_corr_lt11 _ _ _ _ rf_bb_ex rf_bbT_N_ex.

Definition rf_src_refine_bound_on_total_hep_workload := ltac:(src_ty Rq.refine_bound_on_total_hep_workload).
Definition rf_tgt_refine_bound_on_total_hep_workload :=
  ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_bound_on_total_hep_workload).
Definition refine_bound_on_total_hep_workload_correspondence :
  TypeCorrespondence rf_src_refine_bound_on_total_hep_workload rf_tgt_refine_bound_on_total_hep_workload :=
  rf_corr_lt111 _ _ _ _ rf_botw_ex rf_botwT_N_ex.

Definition rf_src_refine_check_point_FP := ltac:(src_ty Rq.refine_check_point_FP).
Definition rf_tgt_refine_check_point_FP := ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_check_point_FP).
Definition refine_check_point_FP_correspondence : TypeCorrespondence rf_src_refine_check_point_FP rf_tgt_refine_check_point_FP :=
  rf_corr_lt1p _ _ _ _ rf_cpFP_ex rf_cpFPT_N_ex.

Definition rf_src_refine_check_point_FP' := ltac:(src_ty Rq.refine_check_point_FP').
Definition rf_tgt_refine_check_point_FP' := ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_check_point_FP').
Definition refine_check_point_FP'_correspondence :
  TypeCorrespondence rf_src_refine_check_point_FP' rf_tgt_refine_check_point_FP' :=
  rf_corr_TT1p _ _ _ _ rf_cpFP_ex rf_cpFPT_N_ex.

Definition rf_src_refine_check_point_NP := ltac:(src_ty Rq.refine_check_point_NP).
Definition rf_tgt_refine_check_point_NP := ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_check_point_NP).
Definition refine_check_point_NP_correspondence : TypeCorrespondence rf_src_refine_check_point_NP rf_tgt_refine_check_point_NP :=
  rf_corr_lt1p _ _ _ _ rf_cpNP_ex rf_cpNPT_N_ex.

Definition rf_src_refine_check_point_NP' := ltac:(src_ty Rq.refine_check_point_NP').
Definition rf_tgt_refine_check_point_NP' := ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_check_point_NP').
Definition refine_check_point_NP'_correspondence :
  TypeCorrespondence rf_src_refine_check_point_NP' rf_tgt_refine_check_point_NP' :=
  rf_corr_TT1p _ _ _ _ rf_cpNP_ex rf_cpNPT_N_ex.

Definition rf_src_refine_search_space_emax_EDF := ltac:(src_ty Rq.refine_search_space_emax_EDF).
Definition rf_tgt_refine_search_space_emax_EDF :=
  ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_search_space_emax_EDF).
Definition refine_search_space_emax_EDF_correspondence :
  TypeCorrespondence rf_src_refine_search_space_emax_EDF rf_tgt_refine_search_space_emax_EDF :=
  rf_corr_TT1l _ _ _ _ rf_essE_ex rf_ssEN_ex.

Definition rf_src_refine_task_search_space_emax_EDF := ltac:(src_ty Rq.refine_task_search_space_emax_EDF).
Definition rf_tgt_refine_task_search_space_emax_EDF :=
  ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_task_search_space_emax_EDF).
Definition refine_task_search_space_emax_EDF_correspondence :
  TypeCorrespondence rf_src_refine_task_search_space_emax_EDF rf_tgt_refine_task_search_space_emax_EDF :=
  rf_corr_T21l _ _ _ _ rf_etss_ex rf_tssN_ex.

Definition rf_src_refine_total_rbf' := ltac:(src_ty Rq.refine_total_rbf').
Definition rf_tgt_refine_total_rbf' := ltac:(src_ty I.Prosa_Implementation_Refinements_EDF_Refinements_refine_total_rbf').
Definition refine_total_rbf'_correspondence : TypeCorrespondence rf_src_refine_total_rbf' rf_tgt_refine_total_rbf' :=
  rf_corr_TS11 _ _ _ _ rf_trbf_ex rf_trbfT_N_ex.
