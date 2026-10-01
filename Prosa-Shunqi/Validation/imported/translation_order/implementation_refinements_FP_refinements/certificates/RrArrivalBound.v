(* Re-bound copy of the accepted certificates/implementation_refinements_arrival_bound/RefArrivalBoundCorrespondence.v: modules renamed (ImportedRefArrivalBound=ImportedRefFPRefinements,RabBase=RrBase), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(** Correspondences for [implementation/refinements/arrival_bound.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (unchanged). The
    base maps and operation correspondences are those of the accepted refinements.v certificate, re-bound in
    [RrBase]. Here:
    - arrival-curve prefixes, the accepted [task_arrivals_bound] and the generic [task_arrivals_bound_T] are related
      by the constructor-preserving maps (any element map: the identity for generic definitions, the unary or binary
      number maps at [nat]/[N]), with two-way totals for [task_arrivals_bound_T];
    - each definition is related to its translation for related inputs (operation-class instances by their field);
    - the [Type]-valued statements by [TypeCorrespondence] (maps in both directions), the two transitivity lemmas by
      [PropSPropRel].
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.arrival_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefFPRefinements ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RrBase.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefFPRefinements.
Module Rab := prosa.implementation.refinements.arrival_bound.
Module EAC := prosa.implementation.definitions.extrapolated_arrival_curve.
Module AB := prosa.implementation.definitions.arrival_bound.

(** ** Imported names *)
Abbreviation ITab := I.Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T.
Abbreviation IPer := I.Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Periodic_T.
Abbreviation ISpo := I.Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Sporadic_T.
Abbreviation IArr := I.Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_ArrivalPrefix_T.
Abbreviation IAB := I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound.
Abbreviation IABPer := I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic.
Abbreviation IABSpo := I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic.
Abbreviation IABArr := I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix.
Abbreviation Imul_of := I.Prosa_Implementation_Refinements_Refinements_mul_of.
Abbreviation Imul_op := I.Prosa_Implementation_Refinements_Refinements_mul_of_mul_op.
Abbreviation INmul := I.Prosa_Implementation_Refinements_Refinements_N_mul.
Abbreviation IPmul := I.Prosa_Implementation_Refinements_Refinements_Pos_mul.

(** ** Arrival-curve prefixes *)
Definition pfx {A B : Type} (e : A -> B) (p : A * seq (A * A)) : IProd B (IList (IProd B B)) :=
  pre e (lex (pre e e)) p.
Definition pfxi {A B : Type} (i : B -> A) (p : IProd B (IList (IProd B B))) : A * seq (A * A) :=
  pri i (lim (pri i i)) p.

Lemma rf_pfxi_pfx {A B : Type} (e : A -> B) (i : B -> A) (H : forall a, i (e a) = a) p : pfxi i (pfx e p) = p.
Proof.
  case: p => h st. rewrite /pfxi /pfx /pri /pre /= H.
  have -> : lim (pri i i) (lex (pre e e) st) = st.
  { apply: rf_lim_lex => -[a b]. by rewrite /pri /pre /= !H. }
  by [].
Qed.

Lemma rf_pfx_pfxi {A B : Type} (e : A -> B) (i : B -> A) (H : forall b, Lean.eq (e (i b)) b) p :
  Lean.eq (pfx e (pfxi i p)) p.
Proof.
  refine (rf_pair_eq _ _ _ _ (H _) _).
  apply rf_lex_lim. intro q. exact (rf_pair_eq _ _ _ _ (H _) (H _)).
Qed.

(** ** The generic [task_arrivals_bound_T] *)
Definition tabT_ex {A B : Type} (e : A -> B) (x : @Rab.task_arrivals_bound_T A) : ITab B :=
  match x with
  | Rab.Periodic_T a => IPer B (e a)
  | Rab.Sporadic_T a => ISpo B (e a)
  | Rab.ArrivalPrefix_T p => IArr B (pfx e p)
  end.
Definition tabT_im {A B : Type} (i : B -> A) (x : ITab B) : @Rab.task_arrivals_bound_T A :=
  match x with
  | I.Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Periodic_T a => Rab.Periodic_T (i a)
  | I.Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Sporadic_T a => Rab.Sporadic_T (i a)
  | I.Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_ArrivalPrefix_T p =>
      Rab.ArrivalPrefix_T (pfxi i p)
  end.

Lemma rf_tabT_rt {A B : Type} (e : A -> B) (i : B -> A) (H : forall a, i (e a) = a) x : tabT_im i (tabT_ex e x) = x.
Proof. case: x => [a|a|p] /=; by rewrite ?H ?(rf_pfxi_pfx e i H). Qed.
Lemma rf_tabT_rtL {A B : Type} (e : A -> B) (i : B -> A) (H : forall b, Lean.eq (e (i b)) b) x :
  Lean.eq (tabT_ex e (tabT_im i x)) x.
Proof.
  destruct x as [a|a|p]; cbn.
  - exact (rf_congr (IPer B) _ _ (H a)).
  - exact (rf_congr (ISpo B) _ _ (H a)).
  - exact (rf_congr (IArr B) _ _ (rf_pfx_pfxi e i H p)).
Qed.

Definition TabTRel {A : Type} (x : @Rab.task_arrivals_bound_T A) (y : ITab A) : SProp := Lean.eq (tabT_ex idr x) y.

Lemma task_arrivals_bound_T_source_total (A : Type) (x : @Rab.task_arrivals_bound_T A) : TabTRel x (tabT_ex idr x).
Proof. exact (rf_refl _). Qed.

Lemma task_arrivals_bound_T_target_total (A : Type) (y : ITab A) : TabTRel (tabT_im idr y) y.
Proof. exact (rf_tabT_rtL idr idr rf_idr_rtL y). Qed.

(** ** The accepted [task_arrivals_bound] *)
Definition ab_ex (x : AB.task_arrivals_bound) : IAB :=
  match x with
  | AB.Periodic n => IABPer (ne n)
  | AB.Sporadic n => IABSpo (ne n)
  | AB.ArrivalPrefix p => IABArr (pfx ne p)
  end.
Definition ab_im (x : IAB) : AB.task_arrivals_bound :=
  match x with
  | I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic n => AB.Periodic (ni n)
  | I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic n => AB.Sporadic (ni n)
  | I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix p => AB.ArrivalPrefix (pfxi ni p)
  end.
Lemma rf_ab_rt x : ab_im (ab_ex x) = x.
Proof. case: x => [n|n|p] /=; by rewrite ?rf_ni_ne ?(rf_pfxi_pfx ne ni rf_ni_ne). Qed.
Lemma rf_ab_rtL x : Lean.eq (ab_ex (ab_im x)) x.
Proof.
  destruct x as [n|n|p]; cbn.
  - exact (rf_congr IABPer _ _ (rf_ne_ni n)).
  - exact (rf_congr IABSpo _ _ (rf_ne_ni n)).
  - exact (rf_congr IABArr _ _ (rf_pfx_pfxi ne ni rf_ne_ni p)).
Qed.

(** ** List helpers: MathComp [last] and [getLastD], [path]/[sorted] and [sortedBool], [has] and [any] *)
Lemma rf_getLastD_cons_ex {A C : Type} (eA : A -> C) y ys d :
  Lean.eq (eA (last y ys)) (I.List_getLastD_inst1 C (Icons C (eA y) (lex eA ys)) d).
Proof.
  revert y d; induction ys as [|z zs IH]; intros y d.
  - exact (rf_refl _).
  - exact (IH z d).
Qed.

Lemma rf_getLastD_ex {A C : Type} (eA : A -> C) d xs :
  Lean.eq (eA (last d xs)) (I.List_getLastD_inst1 C (lex eA xs) (eA d)).
Proof. destruct xs as [|y ys]; [exact (rf_refl _) | exact (rf_getLastD_cons_ex eA y ys (eA d))]. Qed.

Lemma rf_path_ex {A C : Type} (eA : A -> C) (r : A -> A -> bool) (rL : C -> C -> I.Bool)
    (Hr : forall a b, Lean.eq (be (r a b)) (rL (eA a) (eA b))) x xs :
  Lean.eq (be (path r x xs)) (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBoolFrom_inst1 C rL (eA x) (lex eA xs)).
Proof.
  revert x; induction xs as [|y ys IH]; intro x; cbn [path lex].
  - exact (rf_refl _).
  - change (Lean.eq (be (r x y && path r y ys))
      (I.Bool_and (rL (eA x) (eA y))
         (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBoolFrom_inst1 C rL (eA y) (lex eA ys)))).
    have H1 := Hr x y. rf_rw H1. have H2 := IH y. rf_rw H2.
    destruct (r x y); destruct (path r y ys); exact (rf_refl _).
Qed.

Lemma rf_sorted_ex {A C : Type} (eA : A -> C) (r : A -> A -> bool) (rL : C -> C -> I.Bool)
    (Hr : forall a b, Lean.eq (be (r a b)) (rL (eA a) (eA b))) xs :
  Lean.eq (be (sorted r xs)) (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1 C rL (lex eA xs)).
Proof. destruct xs as [|x xs]; [exact (rf_refl _) | exact (rf_path_ex eA r rL Hr x xs)]. Qed.

Lemma rf_has_ex {A C : Type} (eA : A -> C) (P : A -> bool) (PL : C -> I.Bool)
    (HP : forall a, Lean.eq (be (P a)) (PL (eA a))) xs :
  Lean.eq (be (has P xs)) (I.List_any_inst1 C (lex eA xs) PL).
Proof.
  induction xs as [|x xs IH]; cbn [has lex].
  - exact (rf_refl _).
  - change (Lean.eq (be (P x || has P xs)) (I.Bool_or (PL (eA x)) (I.List_any_inst1 C (lex eA xs) PL))).
    have Hx := HP x. rf_rw Hx. rf_rw IH.
    destruct (P x); destruct (has P xs); exact (rf_refl _).
Qed.

(** ** Generic definitions (element types by identity, operation classes by their field) *)
Definition PfxRel {T : Type} (pR : T * seq (T * T)) (pL : IProd T (IList (IProd T T))) : SProp :=
  Lean.eq (pfx idr pR) pL.

Lemma rf_and_ex a b : Lean.eq (be (a && b)) (I.Bool_and (be a) (be b)).
Proof. destruct a; destruct b; exact (rf_refl _). Qed.

Lemma taskab_eqdef_T_correspondence (T : Type) (eR : eq_of T) eL (pR : eq_of (T * seq (T * T))) pL :
  BOpRel eR (Ieq_op T eL) ->
  (forall x y, Lean.eq (be (pR x y)) (Ieq_op (IProd T (IList (IProd T T))) pL (pfx idr x) (pfx idr y))) ->
  forall xR xL yR yL, TabTRel xR xL -> TabTRel yR yL ->
  Lean.eq (be (@Rab.taskab_eqdef_T T eR pR xR yR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_taskab_eqdef_T T eL pL xL yL).
Proof.
  intros He Hp xR xL yR yL Hx Hy. destruct Hx. destruct Hy.
  destruct xR as [a|a|p]; destruct yR as [b|b|q]; cbn [tabT_ex];
    first [ exact (He a b) | exact (Hp p q) | exact (rf_refl _) ].
Qed.

Lemma horizon_of_T_correspondence (T : Type) pR pL :
  @PfxRel T pR pL -> Lean.eq (Rab.horizon_of_T pR) (I.Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T T pL).
Proof. intro H. destruct H. destruct pR. exact (rf_refl _). Qed.

Lemma steps_of_T_correspondence (T : Type) pR pL :
  @PfxRel T pR pL ->
  Lean.eq (lex (pre idr idr) (Rab.steps_of_T pR)) (I.Prosa_Implementation_Refinements_ArrivalBound_steps_of_T T pL).
Proof. intro H. destruct H. destruct pR. exact (rf_refl _). Qed.

Lemma rf_time_steps_of_T_ex (T : Type) pR :
  Lean.eq (lex idr (Rab.time_steps_of_T pR)) (I.Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T T (pfx idr pR)).
Proof. destruct pR as [h st]. exact (rf_map_ex (pre idr idr) idr _ (I.Prod_fst_inst3 T T) (fun a => rf_refl _) st). Qed.

Lemma time_steps_of_T_correspondence (T : Type) pR pL :
  @PfxRel T pR pL ->
  Lean.eq (lex idr (Rab.time_steps_of_T pR)) (I.Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T T pL).
Proof. intro H. destruct H. exact (rf_time_steps_of_T_ex T pR). Qed.

Lemma rf_step_at_T_ex (T : Type) (zR : zero_of T) zL (lR : leq_of T) lL :
  ZeroRel zR zL -> BOpRel lR (Ileq_op T lL) -> forall pR tR,
  Lean.eq (pre idr idr (@Rab.step_at_T T zR lR pR tR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_step_at_T T zL lL (pfx idr pR) tR).
Proof.
  intros Hz Hl pR tR. destruct pR as [h st].
  unfold Rab.step_at_T, I.Prosa_Implementation_Refinements_ArrivalBound_step_at_T.
  refine (rf_trans _ _ _ (rf_getLastD_ex (pre idr idr) (zR, zR) _) _).
  refine (rf_congr2 (I.List_getLastD_inst1 (IProd T T)) _ _ _ _ _ _).
  - exact (rf_filter_ex (pre idr idr) (fun step => lR step.1 tR)
      (fun s => Ileq_op T lL (I.Prod_fst_inst3 T T s) tR) (fun a => Hl a.1 tR) st).
  - exact (rf_pair_eq _ _ _ _ Hz Hz).
Qed.

Lemma step_at_T_correspondence (T : Type) (zR : zero_of T) zL (lR : leq_of T) lL :
  ZeroRel zR zL -> BOpRel lR (Ileq_op T lL) -> forall pR pL tR tL, @PfxRel T pR pL -> Lean.eq tR tL ->
  Lean.eq (pre idr idr (@Rab.step_at_T T zR lR pR tR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_step_at_T T zL lL pL tL).
Proof. intros Hz Hl pR pL tR tL Hp Ht. destruct Hp. destruct Ht. exact (rf_step_at_T_ex T zR zL lR lL Hz Hl pR tR). Qed.

Lemma rf_value_at_T_ex (T : Type) (zR : zero_of T) zL (lR : leq_of T) lL :
  ZeroRel zR zL -> BOpRel lR (Ileq_op T lL) -> forall pR tR,
  Lean.eq (@Rab.value_at_T T zR lR pR tR)
          (I.Prosa_Implementation_Refinements_ArrivalBound_value_at_T T zL lL (pfx idr pR) tR).
Proof. intros Hz Hl pR tR. exact (rf_congr (I.Prod_snd_inst3 T T) _ _ (rf_step_at_T_ex T zR zL lR lL Hz Hl pR tR)). Qed.

Lemma value_at_T_correspondence (T : Type) (zR : zero_of T) zL (lR : leq_of T) lL :
  ZeroRel zR zL -> BOpRel lR (Ileq_op T lL) -> forall pR pL tR tL, @PfxRel T pR pL -> Lean.eq tR tL ->
  Lean.eq (@Rab.value_at_T T zR lR pR tR)
          (I.Prosa_Implementation_Refinements_ArrivalBound_value_at_T T zL lL pL tL).
Proof. intros Hz Hl pR pL tR tL Hp Ht. destruct Hp. destruct Ht. exact (rf_value_at_T_ex T zR zL lR lL Hz Hl pR tR). Qed.

Lemma extrapolated_arrival_curve_T_correspondence (T : Type) (zR : zero_of T) zL (aR : add_of T) aL
    (mR : mul_of T) mL (dR : div_of T) dL (oR : mod_of T) oL (lR : leq_of T) lL :
  ZeroRel zR zL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel oR (Imod_op T oL) -> BOpRel lR (Ileq_op T lL) ->
  forall pR pL tR tL, @PfxRel T pR pL -> Lean.eq tR tL ->
  Lean.eq (@Rab.extrapolated_arrival_curve_T T zR aR mR dR oR lR pR tR)
          (I.Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T T zL aL mL dL oL lL pL tL).
Proof.
  intros Hz Ha Hm Hd Ho Hl pR pL tR tL Hp Ht. destruct Hp. destruct Ht.
  unfold Rab.extrapolated_arrival_curve_T, I.Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T.
  cbv zeta.
  have Hh := horizon_of_T_correspondence T pR _ (rf_refl (pfx idr pR)).
  set h := Rab.horizon_of_T pR. set hL := I.Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T T (pfx idr pR).
  refine (rf_trans _ _ _ (Ha _ _) (rf_congr2 (Iadd_op T aL) _ _ _ _ _ _)).
  - refine (rf_trans _ _ _ (Hm _ _) (rf_congr2 (Imul_op T mL) _ _ _ _ _ _)).
    + exact (rf_trans _ _ _ (Hd _ _) (rf_congr (Idiv_op T dL tR) _ _ Hh)).
    + exact (rf_trans _ _ _ (rf_value_at_T_ex T zR zL lR lL Hz Hl pR h)
        (rf_congr (I.Prosa_Implementation_Refinements_ArrivalBound_value_at_T T zL lL (pfx idr pR)) _ _ Hh)).
  - exact (rf_trans _ _ _ (rf_value_at_T_ex T zR zL lR lL Hz Hl pR _)
      (rf_congr (I.Prosa_Implementation_Refinements_ArrivalBound_value_at_T T zL lL (pfx idr pR)) _ _
        (rf_trans _ _ _ (Ho _ _) (rf_congr (Imod_op T oL tR) _ _ Hh)))).
Qed.

Lemma rf_ltn_steps_T_ex (T : Type) (lR : lt_of T) lL :
  BOpRel lR (Ilt_op T lL) -> forall a b,
  Lean.eq (be (@Rab.ltn_steps_T T lR a b))
          (I.Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T T lL (pre idr idr a) (pre idr idr b)).
Proof.
  intros Hl a b. unfold Rab.ltn_steps_T.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (Hl _ _) (Hl _ _))).
Qed.

Lemma ltn_steps_T_correspondence (T : Type) (lR : lt_of T) lL :
  BOpRel lR (Ilt_op T lL) -> forall aR aL bR bL, Lean.eq (pre idr idr aR) aL -> Lean.eq (pre idr idr bR) bL ->
  Lean.eq (be (@Rab.ltn_steps_T T lR aR bR)) (I.Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T T lL aL bL).
Proof. intros Hl aR aL bR bL Ha Hb. destruct Ha. destruct Hb. exact (rf_ltn_steps_T_ex T lR lL Hl aR bR). Qed.

Lemma rf_leq_steps_T_ex (T : Type) (lR : leq_of T) lL :
  BOpRel lR (Ileq_op T lL) -> forall a b,
  Lean.eq (be (@Rab.leq_steps_T T lR a b))
          (I.Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T T lL (pre idr idr a) (pre idr idr b)).
Proof.
  intros Hl a b. unfold Rab.leq_steps_T.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (Hl _ _) (Hl _ _))).
Qed.

Lemma leq_steps_T_correspondence (T : Type) (lR : leq_of T) lL :
  BOpRel lR (Ileq_op T lL) -> forall aR aL bR bL, Lean.eq (pre idr idr aR) aL -> Lean.eq (pre idr idr bR) bL ->
  Lean.eq (be (@Rab.leq_steps_T T lR aR bR)) (I.Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T T lL aL bL).
Proof. intros Hl aR aL bR bL Ha Hb. destruct Ha. destruct Hb. exact (rf_leq_steps_T_ex T lR lL Hl aR bR). Qed.

Lemma rf_sorted_ltn_steps_T_ex (T : Type) (lR : lt_of T) lL :
  BOpRel lR (Ilt_op T lL) -> forall pR,
  Lean.eq (be (@Rab.sorted_ltn_steps_T T lR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_sorted_ltn_steps_T T lL (pfx idr pR)).
Proof.
  intros Hl [h st].
  exact (rf_sorted_ex (pre idr idr) (@Rab.ltn_steps_T T lR) _ (rf_ltn_steps_T_ex T lR lL Hl) st).
Qed.

Lemma sorted_ltn_steps_T_correspondence (T : Type) (lR : lt_of T) lL :
  BOpRel lR (Ilt_op T lL) -> forall pR pL, @PfxRel T pR pL ->
  Lean.eq (be (@Rab.sorted_ltn_steps_T T lR pR)) (I.Prosa_Implementation_Refinements_ArrivalBound_sorted_ltn_steps_T T lL pL).
Proof. intros Hl pR pL Hp. destruct Hp. exact (rf_sorted_ltn_steps_T_ex T lR lL Hl pR). Qed.

Lemma rf_positive_horizon_T_ex (T : Type) (zR : zero_of T) zL (lR : lt_of T) lL :
  ZeroRel zR zL -> BOpRel lR (Ilt_op T lL) -> forall pR,
  Lean.eq (be (@Rab.positive_horizon_T T zR lR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_positive_horizon_T T zL lL (pfx idr pR)).
Proof.
  intros Hz Hl [h st]. unfold Rab.positive_horizon_T, I.Prosa_Implementation_Refinements_ArrivalBound_positive_horizon_T.
  have Hz' : Lean.eq zR (Izero_op T zL) := Hz.
  exact (rf_trans _ _ _ (Hl zR h) (rf_congr (fun z => Ilt_op T lL z h) _ _ Hz')).
Qed.

Lemma positive_horizon_T_correspondence (T : Type) (zR : zero_of T) zL (lR : lt_of T) lL :
  ZeroRel zR zL -> BOpRel lR (Ilt_op T lL) -> forall pR pL, @PfxRel T pR pL ->
  Lean.eq (be (@Rab.positive_horizon_T T zR lR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_positive_horizon_T T zL lL pL).
Proof. intros Hz Hl pR pL Hp. destruct Hp. exact (rf_positive_horizon_T_ex T zR zL lR lL Hz Hl pR). Qed.

Lemma rf_large_horizon_T_ex (T : Type) (lR : leq_of T) lL :
  BOpRel lR (Ileq_op T lL) -> forall pR,
  Lean.eq (be (@Rab.large_horizon_T T lR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_large_horizon_T T lL (pfx idr pR)).
Proof.
  intros Hl pR. unfold Rab.large_horizon_T, I.Prosa_Implementation_Refinements_ArrivalBound_large_horizon_T.
  refine (rf_trans _ _ _ (rf_all_ex idr _ (fun s => Ileq_op T lL s (Rab.horizon_of_T pR)) (fun a => Hl a _) _) _).
  have Ht := rf_time_steps_of_T_ex T pR. rf_rw Ht.
  have Hh := horizon_of_T_correspondence T pR _ (rf_refl (pfx idr pR)). rf_rw Hh.
  exact (rf_refl _).
Qed.

Lemma large_horizon_T_correspondence (T : Type) (lR : leq_of T) lL :
  BOpRel lR (Ileq_op T lL) -> forall pR pL, @PfxRel T pR pL ->
  Lean.eq (be (@Rab.large_horizon_T T lR pR)) (I.Prosa_Implementation_Refinements_ArrivalBound_large_horizon_T T lL pL).
Proof. intros Hl pR pL Hp. destruct Hp. exact (rf_large_horizon_T_ex T lR lL Hl pR). Qed.

Lemma rf_no_inf_arrivals_T_ex (T : Type) (zR : zero_of T) zL (eR : eq_of T) eL (lR : leq_of T) lL :
  ZeroRel zR zL -> BOpRel eR (Ieq_op T eL) -> BOpRel lR (Ileq_op T lL) -> forall pR,
  Lean.eq (be (@Rab.no_inf_arrivals_T T zR eR lR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_no_inf_arrivals_T T zL eL lL (pfx idr pR)).
Proof.
  intros Hz He Hl pR. unfold Rab.no_inf_arrivals_T, I.Prosa_Implementation_Refinements_ArrivalBound_no_inf_arrivals_T.
  have Hz' : Lean.eq zR (Izero_op T zL) := Hz.
  refine (rf_trans _ _ _ (He _ _) (rf_congr2 (Ieq_op T eL) _ _ _ _ _ Hz')).
  exact (rf_trans _ _ _ (rf_value_at_T_ex T zR zL lR lL Hz Hl pR zR)
    (rf_congr (I.Prosa_Implementation_Refinements_ArrivalBound_value_at_T T zL lL (pfx idr pR)) _ _ Hz')).
Qed.

Lemma no_inf_arrivals_T_correspondence (T : Type) (zR : zero_of T) zL (eR : eq_of T) eL (lR : leq_of T) lL :
  ZeroRel zR zL -> BOpRel eR (Ieq_op T eL) -> BOpRel lR (Ileq_op T lL) -> forall pR pL, @PfxRel T pR pL ->
  Lean.eq (be (@Rab.no_inf_arrivals_T T zR eR lR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_no_inf_arrivals_T T zL eL lL pL).
Proof. intros Hz He Hl pR pL Hp. destruct Hp. exact (rf_no_inf_arrivals_T_ex T zR zL eR eL lR lL Hz He Hl pR). Qed.

Lemma rf_specified_bursts_T_ex (T : Type) (oR : one_of T) oL (eR : eq_of T) eL :
  OneRel oR oL -> BOpRel eR (Ieq_op T eL) -> forall pR,
  Lean.eq (be (@Rab.specified_bursts_T T oR eR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_specified_bursts_T T oL eL (pfx idr pR)).
Proof.
  intros Ho He pR. unfold Rab.specified_bursts_T, I.Prosa_Implementation_Refinements_ArrivalBound_specified_bursts_T.
  have Ho' : Lean.eq oR (Ione_op T oL) := Ho.
  refine (rf_trans _ _ _ (rf_has_ex idr _ (fun s => Ieq_op T eL s oR) (fun a => He a oR) _) _).
  have Ht := rf_time_steps_of_T_ex T pR. rf_rw Ht. rf_rw Ho'.
  exact (rf_refl _).
Qed.

Lemma specified_bursts_T_correspondence (T : Type) (oR : one_of T) oL (eR : eq_of T) eL :
  OneRel oR oL -> BOpRel eR (Ieq_op T eL) -> forall pR pL, @PfxRel T pR pL ->
  Lean.eq (be (@Rab.specified_bursts_T T oR eR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_specified_bursts_T T oL eL pL).
Proof. intros Ho He pR pL Hp. destruct Hp. exact (rf_specified_bursts_T_ex T oR oL eR eL Ho He pR). Qed.

Lemma valid_extrapolated_arrival_curve_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL
    (eR : eq_of T) eL (lR : leq_of T) lL (tR : lt_of T) tL :
  ZeroRel zR zL -> OneRel oR oL -> BOpRel eR (Ieq_op T eL) -> BOpRel lR (Ileq_op T lL) -> BOpRel tR (Ilt_op T tL) ->
  forall pR pL, @PfxRel T pR pL ->
  Lean.eq (be (@Rab.valid_extrapolated_arrival_curve_T T zR oR eR lR tR pR))
          (I.Prosa_Implementation_Refinements_ArrivalBound_valid_extrapolated_arrival_curve_T T zL oL eL lL tL pL).
Proof.
  intros Hz Ho He Hl Ht pR pL Hp. destruct Hp.
  unfold Rab.valid_extrapolated_arrival_curve_T,
    I.Prosa_Implementation_Refinements_ArrivalBound_valid_extrapolated_arrival_curve_T.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_sorted_ltn_steps_T_ex T tR tL Ht pR))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_specified_bursts_T_ex T oR oL eR eL Ho He pR))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_no_inf_arrivals_T_ex T zR zL eR eL lR lL Hz He Hl pR))).
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _
    (rf_positive_horizon_T_ex T zR zL tR tL Hz Ht pR) (rf_large_horizon_T_ex T lR lL Hl pR))).
Qed.

(** ** Definitions at the binary numbers *)
Abbreviation IACPT := I.Prosa_Implementation_Refinements_ArrivalBound_ACPrefixT_to_ACPrefix.
Abbreviation IACPN := I.Prosa_Implementation_Refinements_ArrivalBound_ACPrefix_to_ACPrefixT.
Abbreviation IabT2ab := I.Prosa_Implementation_Refinements_ArrivalBound_task_abT_to_task_ab.
Abbreviation Iab2abT := I.Prosa_Implementation_Refinements_ArrivalBound_task_ab_to_task_abT.

Lemma rf_ACPT_ex x : Lean.eq (pfx ne (Rab.ACPrefixT_to_ACPrefix x)) (IACPT (pfx Ne_ x)).
Proof.
  destruct x as [h st].
  exact (rf_pair_eq _ _ _ _ (rf_nat_of_bin_ex h) (m_tb2tn_correspondence st _ (rf_refl _))).
Qed.

Lemma ACPrefixT_to_ACPrefix_correspondence xR xL :
  Lean.eq (pfx Ne_ xR) xL -> Lean.eq (pfx ne (Rab.ACPrefixT_to_ACPrefix xR)) (IACPT xL).
Proof. intro H. destruct H. exact (rf_ACPT_ex xR). Qed.

Lemma rf_ACPN_ex x : Lean.eq (pfx Ne_ (Rab.ACPrefix_to_ACPrefixT x)) (IACPN (pfx ne x)).
Proof.
  destruct x as [h st].
  exact (rf_pair_eq _ _ _ _ (rf_bin_of_nat_ex h) (m_tn2tb_correspondence st _ (rf_refl _))).
Qed.

Lemma ACPrefix_to_ACPrefixT_correspondence xR xL :
  Lean.eq (pfx ne xR) xL -> Lean.eq (pfx Ne_ (Rab.ACPrefix_to_ACPrefixT xR)) (IACPN xL).
Proof. intro H. destruct H. exact (rf_ACPN_ex xR). Qed.

Lemma rf_abT2ab_ex x : Lean.eq (ab_ex (Rab.task_abT_to_task_ab x)) (IabT2ab (tabT_ex Ne_ x)).
Proof.
  destruct x as [p|m|e]; cbn [Rab.task_abT_to_task_ab ab_ex tabT_ex].
  - exact (rf_congr IABPer _ _ (rf_nat_of_bin_ex p)).
  - exact (rf_congr IABSpo _ _ (rf_nat_of_bin_ex m)).
  - exact (rf_congr IABArr _ _ (rf_ACPT_ex e)).
Qed.

Lemma task_abT_to_task_ab_correspondence xR xL :
  Lean.eq (tabT_ex Ne_ xR) xL -> Lean.eq (ab_ex (Rab.task_abT_to_task_ab xR)) (IabT2ab xL).
Proof. intro H. destruct H. exact (rf_abT2ab_ex xR). Qed.

Lemma rf_ab2abT_ex x : Lean.eq (tabT_ex Ne_ (Rab.task_ab_to_task_abT x)) (Iab2abT (ab_ex x)).
Proof.
  destruct x as [p|m|e]; cbn [Rab.task_ab_to_task_abT ab_ex tabT_ex].
  - exact (rf_congr (IPer IN) _ _ (rf_bin_of_nat_ex p)).
  - exact (rf_congr (ISpo IN) _ _ (rf_bin_of_nat_ex m)).
  - exact (rf_congr (IArr IN) _ _ (rf_ACPN_ex e)).
Qed.

Lemma task_ab_to_task_abT_correspondence xR xL :
  Lean.eq (ab_ex xR) xL -> Lean.eq (tabT_ex Ne_ (Rab.task_ab_to_task_abT xR)) (Iab2abT xL).
Proof. intro H. destruct H. exact (rf_ab2abT_ex xR). Qed.

(** The two [Type]-valued relations: maps in both directions between the related relation instances. *)
Definition RArrivalCurvePrefix_correspondence aR aL xR xL :
  Lean.eq (pfx ne aR) aL -> Lean.eq (pfx Ne_ xR) xL ->
  TypeCorrespondence (Rab.RArrivalCurvePrefix aR xR)
    (I.Prosa_Implementation_Refinements_ArrivalBound_RArrivalCurvePrefix aL xL).
Proof.
  intros Ha Hx. destruct Ha. destruct Hx. split.
  - intro H. apply I.PLift_up_inst1.
    exact (rf_trans _ _ _ (rf_sym _ _ (rf_ACPT_ex xR))
      (rf_of_coq (f_equal (pfx ne) (H : Logic.eq (Rab.ACPrefixT_to_ACPrefix xR) aR)))).
  - intro H. have h := I.PLift_down_inst1 _ H.
    have h2 := f_equal (pfxi ni) (rf_to_coq (rf_trans _ _ _ (rf_ACPT_ex xR) h)).
    rewrite !(rf_pfxi_pfx ne ni rf_ni_ne) in h2. exact h2.
Defined.

Definition Rtask_ab_correspondence aR aL xR xL :
  Lean.eq (ab_ex aR) aL -> Lean.eq (tabT_ex Ne_ xR) xL ->
  TypeCorrespondence (Rab.Rtask_ab aR xR) (I.Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab aL xL).
Proof.
  intros Ha Hx. destruct Ha. destruct Hx. split.
  - intro H. apply I.PLift_up_inst1.
    exact (rf_trans _ _ _ (rf_sym _ _ (rf_abT2ab_ex xR))
      (rf_of_coq (f_equal ab_ex (H : Logic.eq (Rab.task_abT_to_task_ab xR) aR)))).
  - intro H. have h := I.PLift_down_inst1 _ H.
    have h2 := f_equal ab_im (rf_to_coq (rf_trans _ _ _ (rf_abT2ab_ex xR) h)).
    rewrite !rf_ab_rt in h2. exact h2.
Defined.

(** The equality instances: a MathComp equality test against the Lean decision of the equality of the images. *)
Lemma rf_inj_rel {A B : Type} (e : A -> B) (i : B -> A) (H : forall a, i (e a) = a) (x y : A) :
  PropSPropRel (x = y) (Lean.eq (e x) (e y)).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hxy. exact (rf_of_coq (f_equal e Hxy)).
  - intro Hxy. apply strictly_inhabits.
    have h := f_equal i (rf_to_coq Hxy). by rewrite !H in h.
Qed.

Lemma rf_eqtype_rel {A : eqType} {B : Type} (e : A -> B) (i : B -> A) (H : forall a, i (e a) = a) (x y : A) :
  PropSPropRel (is_true (x == y)) (Lean.eq (e x) (e y)).
Proof.
  have R := rf_inj_rel e i H x y.
  apply prop_sprop_rel_intro.
  - intro Hxy. exact (prop_to_sprop _ _ R (eqP Hxy)).
  - intro Hxy. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ R Hxy).
Qed.

Abbreviation IeqL := I.Prosa_Implementation_Refinements_ArrivalBound_eq_listN.
Abbreviation IeqP := I.Prosa_Implementation_Refinements_ArrivalBound_eq_NlistNN.
Abbreviation IeqT := I.Prosa_Implementation_Refinements_ArrivalBound_eq_taskab.

Lemma rf_eq_listN_ex x y : Lean.eq (be (Rab.eq_listN x y)) (Ieq_op (IList IN) IeqL (lex Ne_ x) (lex Ne_ y)).
Proof. exact (rf_decide_ex _ _ _ (rf_eqtype_rel (lex Ne_) (lim Ni) (rf_lim_lex Ne_ Ni rf_Ni_Ne) x y)). Qed.

Lemma eq_listN_correspondence xR xL yR yL :
  Lean.eq (lex Ne_ xR) xL -> Lean.eq (lex Ne_ yR) yL ->
  Lean.eq (be (Rab.eq_listN xR yR)) (Ieq_op (IList IN) IeqL xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_eq_listN_ex xR yR). Qed.

Lemma rf_eq_NlistNN_ex x y :
  Lean.eq (be (Rab.eq_NlistNN x y)) (Ieq_op (IProd IN (IList (IProd IN IN))) IeqP (pfx Ne_ x) (pfx Ne_ y)).
Proof.
  exact (rf_decide_ex _ _ _ (@rf_eqtype_rel (Datatypes_prod__canonical__eqtype_Equality _ _) _
    (pfx Ne_) (pfxi Ni) (rf_pfxi_pfx Ne_ Ni rf_Ni_Ne) x y)).
Qed.

Lemma eq_NlistNN_correspondence xR xL yR yL :
  Lean.eq (pfx Ne_ xR) xL -> Lean.eq (pfx Ne_ yR) yL ->
  Lean.eq (be (Rab.eq_NlistNN xR yR)) (Ieq_op (IProd IN (IList (IProd IN IN))) IeqP xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_eq_NlistNN_ex xR yR). Qed.

Lemma rf_eq_taskab_ex x y :
  Lean.eq (be (Rab.eq_taskab x y)) (Ieq_op (ITab IN) IeqT (tabT_ex Ne_ x) (tabT_ex Ne_ y)).
Proof.
  destruct x as [a|a|p]; destruct y as [b|b|q]; cbn [tabT_ex];
    first [ exact (rf_N_eqb_ex a b) | exact (rf_eq_NlistNN_ex p q) | exact (rf_refl _) ].
Qed.

Lemma eq_taskab_correspondence xR xL yR yL :
  Lean.eq (tabT_ex Ne_ xR) xL -> Lean.eq (tabT_ex Ne_ yR) yL ->
  Lean.eq (be (Rab.eq_taskab xR yR)) (Ieq_op (ITab IN) IeqT xL yL).
Proof. intros Hx Hy. destruct Hx. destruct Hy. exact (rf_eq_taskab_ex xR yR). Qed.

(** ** Statement correspondences *)
Lemma rf_mul_pos_ex p q : Lean.eq (pe (Pos.mul p q)) (IPmul (pe p) (pe q)).
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.mul pe].
  - exact (rf_trans _ _ _ (sfst (rf_add_pos_ex q (xO (Pos.mul p q)))) (rf_congr (IPadd (pe q)) _ _ (rf_congr IxO _ _ IH))).
  - exact (rf_congr IxO _ _ IH).
  - exact (rf_refl _).
Qed.

Lemma rf_N_mul_ex a b : Lean.eq (Ne_ (N.mul a b)) (INmul (Ne_ a) (Ne_ b)).
Proof.
  destruct a as [|p]; destruct b as [|q]; try exact (rf_refl _).
  exact (rf_congr INpos _ _ (rf_mul_pos_ex p q)).
Qed.

Lemma rf_mul_ex a b : Lean.eq (ne (a * b)) (rf_mul (ne a) (ne b)).
Proof. exact (rf_sym _ _ (sub_mul_canonical a b)). Qed.

(** The prefix relation [prod_R Rnat (list_R (prod_R Rnat Rnat))]. *)
Abbreviation pfxR := (prod_R Rnat (list_R pRR)).
Abbreviation IpfxR := (IpR LN IN IRnat (IList (IProd LN LN)) (IList (IProd IN IN)) (IlR (IProd LN LN) (IProd IN IN) IpRR)).
Definition pfxR_fw p p' (H : pfxR p p') : IpfxR (pfx ne p) (pfx Ne_ p') :=
  prodR_fw ne Ne_ (lex (pre ne ne)) (lex (pre Ne_ Ne_)) Rnat IRnat (list_R pRR) (IlR _ _ IpRR) rnat_fw
    (listR_fw (pre ne ne) (pre Ne_ Ne_) pRR IpRR prr_fw) p p' H.
Definition pfxR_bw p p' (H : IpfxR p p') : pfxR (pfxi ni p) (pfxi Ni p') :=
  prodR_bw ni Ni (lim (pri ni ni)) (lim (pri Ni Ni)) Rnat IRnat (list_R pRR) (IlR _ _ IpRR) rnat_bw
    (listR_bw (pri ni ni) (pri Ni Ni) pRR IpRR prr_bw) p p' H.
Definition rf_pfx_n p : Lean.eq (pfx ne (pfxi ni p)) p := rf_pfx_pfxi ne ni rf_ne_ni p.
Definition rf_pfx_N p : Lean.eq (pfx Ne_ (pfxi Ni p)) p := rf_pfx_pfxi Ne_ Ni rf_Ne_Ni p.

(** The step orders on both sides. *)
Lemma rf_EAC_leq_steps_ex a b :
  Lean.eq (be (EAC.leq_steps a b))
    (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps (pre ne ne a) (pre ne ne b)).
Proof.
  unfold EAC.leq_steps.
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_le_decide_ex _ _) (rf_le_decide_ex _ _))).
Qed.
Lemma rf_EAC_ltn_steps_ex a b :
  Lean.eq (be (EAC.ltn_steps a b))
    (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps (pre ne ne a) (pre ne ne b)).
Proof.
  unfold EAC.ltn_steps.
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_lt_decide_ex _ _) (rf_lt_decide_ex _ _))).
Qed.
Lemma rf_leq_steps_T_N_ex a b :
  Lean.eq (be (Rab.leq_steps_T a b))
    (I.Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T IN I.Prosa_Implementation_Refinements_Refinements_leq_N
       (pre Ne_ Ne_ a) (pre Ne_ Ne_ b)).
Proof.
  unfold Rab.leq_steps_T.
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_N_leb_ex _ _) (rf_N_leb_ex _ _))).
Qed.
Lemma rf_ltn_steps_T_N_ex a b :
  Lean.eq (be (Rab.ltn_steps_T a b))
    (I.Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T IN I.Prosa_Implementation_Refinements_Refinements_lt_N
       (pre Ne_ Ne_ a) (pre Ne_ Ne_ b)).
Proof.
  unfold Rab.ltn_steps_T.
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_N_ltb_ex _ _) (rf_N_ltb_ex _ _))).
Qed.

(** Transitivity of the binary step orders. *)
Lemma rf_bool_of (b : bool) (H : Lean.eq (be b) I.Bool_true) : is_true b.
Proof. have h := f_equal bi (rf_to_coq H). by rewrite rf_bi_be in h. Qed.

(** Shape [refines (prod_R Rnat Rnat ==> prod_R Rnat Rnat ==> bool_R) f g]. *)
Definition rf_corr_pp2b (f : nat * nat -> nat * nat -> bool) (g : N * N -> N * N -> bool)
    (fL : IProd LN LN -> IProd LN LN -> I.Bool) (gL : IProd IN IN -> IProd IN IN -> I.Bool)
    (Hf : forall a b, Lean.eq (be (f a b)) (fL (pre ne ne a) (pre ne ne b)))
    (Hg : forall a b, Lean.eq (be (g a b)) (gL (pre Ne_ Ne_ a) (pre Ne_ Ne_ b))) :
  TypeCorrespondence (refines (hrespectful pRR (hrespectful pRR bool_R)) f g)
    (Iref _ _ (Ihr (IProd LN LN) (IProd IN IN) _ _ IpRR (Ihr (IProd LN LN) (IProd IN IN) I.Bool I.Bool IpRR IbR)) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros aL a'L ra bL b'L rb.
    have o := boolR_fw _ _ (rf_ref_out s _ _ (prr_bw _ _ ra) _ _ (prr_bw _ _ rb)).
    refine (rf_tr2 IbR _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (rf_pre_pri_n aL) (rf_pre_pri_n bL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_pre_pri_N a'L) (rf_pre_pri_N b'L))).
  - intro t. apply rf_ref_in. intros a a' ra b b' rb.
    have o := Iref_rel _ _ _ _ _ t _ _ (prr_fw _ _ ra) _ _ (prr_fw _ _ rb).
    apply boolR_bw'.
    exact (rf_tr2 IbR (rf_sym _ _ (Hf a b)) (rf_sym _ _ (Hg a' b')) o).
Defined.

(** Shape [forall xs xs', refines (list_R (prod_R Rnat Rnat)) xs xs' -> refines bool_R (sorted r xs) (sorted r' xs')]. *)
Definition rf_corr_sorted (r : nat * nat -> nat * nat -> bool) (r' : N * N -> N * N -> bool)
    (rL : IProd LN LN -> IProd LN LN -> I.Bool) (r'L : IProd IN IN -> IProd IN IN -> I.Bool)
    (Hr : forall a b, Lean.eq (be (r a b)) (rL (pre ne ne a) (pre ne ne b)))
    (Hr' : forall a b, Lean.eq (be (r' a b)) (r'L (pre Ne_ Ne_ a) (pre Ne_ Ne_ b))) :
  TypeCorrespondence
    (forall xs xs', refines (list_R pRR) xs xs' -> refines bool_R (sorted r xs) (sorted r' xs'))
    (forall xsL xs'L, Iref _ _ (IlR _ _ IpRR) xsL xs'L ->
       Iref I.Bool I.Bool IbR
         (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1 (IProd LN LN) rL xsL)
         (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1 (IProd IN IN) r'L xs'L)).
Proof.
  split.
  - intros s xsL xs'L h. apply Iref_mk.
    have lp := listR_bw (pri ni ni) (pri Ni Ni) pRR IpRR prr_bw _ _ (Iref_rel _ _ _ _ _ h).
    have o := boolR_fw _ _ (rf_ref_out (s _ _ (rf_ref_in lp))).
    refine (rf_tr2 IbR _ _ o).
    + exact (rf_trans _ _ _ (rf_sorted_ex (pre ne ne) r rL Hr _)
        (rf_congr (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1 (IProd LN LN) rL) _ _
          (rf_lex_lim (pre ne ne) (pri ni ni) rf_pre_pri_n xsL))).
    + exact (rf_trans _ _ _ (rf_sorted_ex (pre Ne_ Ne_) r' r'L Hr' _)
        (rf_congr (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1 (IProd IN IN) r'L) _ _
          (rf_lex_lim (pre Ne_ Ne_) (pri Ni Ni) rf_pre_pri_N xs'L))).
  - intros t xs xs' h. apply rf_ref_in.
    have lp := listR_fw (pre ne ne) (pre Ne_ Ne_) pRR IpRR prr_fw _ _ (rf_ref_out h).
    have o := Iref_rel _ _ _ _ _ (t _ _ (Iref_mk _ _ _ _ _ lp)).
    apply boolR_bw'.
    exact (rf_tr2 IbR (rf_sym _ _ (rf_sorted_ex (pre ne ne) r rL Hr xs)) (rf_sym _ _ (rf_sorted_ex (pre Ne_ Ne_) r' r'L Hr' xs')) o).
Defined.

(** The accepted arrival-curve functions and their binary counterparts. *)
Abbreviation Evalue_at := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at.
Abbreviation Avalue_at_N := (I.Prosa_Implementation_Refinements_ArrivalBound_value_at_T IN
  I.Prosa_Implementation_Refinements_Refinements_zero_N I.Prosa_Implementation_Refinements_Refinements_leq_N).

Lemma rf_EAC_value_at_ex p t : Lean.eq (ne (EAC.value_at p t)) (Evalue_at (pfx ne p) (ne t)).
Proof.
  destruct p as [h st].
  change (Lean.eq (I.Prod_snd_inst3 LN LN (pre ne ne (EAC.step_at (h, st) t)))
    (I.Prod_snd_inst3 LN LN (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at (pfx ne (h, st)) (ne t)))).
  refine (rf_congr (I.Prod_snd_inst3 LN LN) _ _ _).
  unfold EAC.step_at, I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at.
  refine (rf_trans _ _ _ (rf_getLastD_ex (pre ne ne) (O, O) _) _).
  refine (rf_congr2 (I.List_getLastD_inst1 (IProd LN LN)) _ _ _ _ _ (rf_refl _)).
  exact (rf_filter_ex (pre ne ne) (fun step => leq step.1 t)
    (fun s => I.Decidable_decide (I.LE_le_inst1 LN I.instLENat (I.Prod_fst_inst3 LN LN s) (ne t))
                (I.Nat_decLe (I.Prod_fst_inst3 LN LN s) (ne t)))
    (fun a => rf_le_decide_ex a.1 t) st).
Qed.

Lemma rf_value_at_T_N_ex p t : Lean.eq (Ne_ (Rab.value_at_T p t)) (Avalue_at_N (pfx Ne_ p) (Ne_ t)).
Proof.
  destruct p as [h st].
  change (Lean.eq (I.Prod_snd_inst3 IN IN (pre Ne_ Ne_ (Rab.step_at_T (h, st) t)))
    (I.Prod_snd_inst3 IN IN (I.Prosa_Implementation_Refinements_ArrivalBound_step_at_T IN
       I.Prosa_Implementation_Refinements_Refinements_zero_N I.Prosa_Implementation_Refinements_Refinements_leq_N
       (pfx Ne_ (h, st)) (Ne_ t)))).
  refine (rf_congr (I.Prod_snd_inst3 IN IN) _ _ _).
  unfold Rab.step_at_T, I.Prosa_Implementation_Refinements_ArrivalBound_step_at_T.
  refine (rf_trans _ _ _ (rf_getLastD_ex (pre Ne_ Ne_) (N0, N0) _) _).
  refine (rf_congr2 (I.List_getLastD_inst1 (IProd IN IN)) _ _ _ _ _ (rf_refl _)).
  exact (rf_filter_ex (pre Ne_ Ne_) (fun step => N.leb step.1 t)
    (fun s => INleb (I.Prod_fst_inst3 IN IN s) (Ne_ t)) (fun a => rf_N_leb_ex a.1 t) st).
Qed.

Lemma rf_EAC_eac_ex p t :
  Lean.eq (ne (EAC.extrapolated_arrival_curve p t))
    (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve (pfx ne p) (ne t)).
Proof.
  destruct p as [h st]. unfold EAC.extrapolated_arrival_curve. cbv zeta.
  refine (rf_trans _ _ _ (rf_add_ex _ _) (rf_congr2 rf_add _ _ _ _ _ _)).
  - refine (rf_trans _ _ _ (rf_mul_ex _ _) (rf_congr2 rf_mul _ _ _ _ (rf_div_ex t h) _)).
    exact (rf_EAC_value_at_ex (h, st) h).
  - refine (rf_trans _ _ _ (rf_EAC_value_at_ex (h, st) _) _).
    exact (rf_congr (Evalue_at (pfx ne (h, st))) _ _ (rf_mod_ex t h)).
Qed.

Lemma rf_eac_T_N_ex p t :
  Lean.eq (Ne_ (Rab.extrapolated_arrival_curve_T p t))
    (I.Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T IN
       I.Prosa_Implementation_Refinements_Refinements_zero_N I.Prosa_Implementation_Refinements_Refinements_add_N
       I.Prosa_Implementation_Refinements_Refinements_mul_N I.Prosa_Implementation_Refinements_Refinements_div_N
       I.Prosa_Implementation_Refinements_Refinements_mod_N I.Prosa_Implementation_Refinements_Refinements_leq_N
       (pfx Ne_ p) (Ne_ t)).
Proof.
  destruct p as [h st]. unfold Rab.extrapolated_arrival_curve_T. cbv zeta.
  refine (rf_trans _ _ _ (rf_N_add_ex _ _) (rf_congr2 INadd _ _ _ _ _ _)).
  - refine (rf_trans _ _ _ (rf_N_mul_ex _ _) (rf_congr2 INmul _ _ _ _ (rf_N_div_ex t h) _)).
    exact (rf_value_at_T_N_ex (h, st) h).
  - refine (rf_trans _ _ _ (rf_value_at_T_N_ex (h, st) _) _).
    exact (rf_congr (Avalue_at_N (pfx Ne_ (h, st))) _ _ (rf_N_mod_ex t h)).
Qed.

(** Shape [refines (prefix ==> Rnat ==> Rnat) f g]. *)
Definition rf_corr_p11 (f : EAC.ArrivalCurvePrefix -> nat -> nat) (g : N * seq (N * N) -> N -> N)
    (fL : IProd LN (IList (IProd LN LN)) -> LN -> LN) (gL : IProd IN (IList (IProd IN IN)) -> IN -> IN)
    (Hf : forall p t, Lean.eq (ne (f p t)) (fL (pfx ne p) (ne t)))
    (Hg : forall p t, Lean.eq (Ne_ (g p t)) (gL (pfx Ne_ p) (Ne_ t))) :
  TypeCorrespondence (refines (hrespectful pfxR (hrespectful Rnat Rnat)) f g)
    (Iref _ _ (Ihr _ _ _ _ IpfxR (Ihr LN IN LN IN IRnat IRnat)) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros pL p'L rp tL t'L rt.
    have o := rnat_fw _ _ (rf_ref_out s _ _ (pfxR_bw _ _ rp) _ _ (rnat_bw _ _ rt)).
    refine (rf_tr2 IRnat _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (rf_pfx_n pL) (rf_ne_ni tL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_pfx_N p'L) (rf_Ne_Ni t'L))).
  - intro t. apply rf_ref_in. intros p p' rp u u' ru.
    have o := Iref_rel _ _ _ _ _ t _ _ (pfxR_fw _ _ rp) _ _ (rnat_fw _ _ ru).
    apply rnat_bw'.
    exact (rf_tr2 IRnat (rf_sym _ _ (Hf p u)) (rf_sym _ _ (Hg p' u')) o).
Defined.

(** [refine_get_time_steps] *)
Lemma rf_EAC_time_steps_ex p :
  Lean.eq (lex ne (EAC.time_steps_of p)) (I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of (pfx ne p)).
Proof. destruct p as [h st]. exact (rf_map_ex (pre ne ne) ne _ (I.Prod_fst_inst3 LN LN) (fun a => rf_refl _) st). Qed.
Lemma rf_time_steps_T_N_ex p :
  Lean.eq (lex Ne_ (Rab.time_steps_of_T p)) (I.Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T IN (pfx Ne_ p)).
Proof. destruct p as [h st]. exact (rf_map_ex (pre Ne_ Ne_) Ne_ _ (I.Prod_fst_inst3 IN IN) (fun a => rf_refl _) st). Qed.

Abbreviation IRtab := I.Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab.

(** [refine_task_ab_eq] *)
Lemma rf_ab_eq_ex (x y : AB.task_arrivals_bound) :
  Lean.eq (be (x == y))
    (I.Decidable_decide (Lean.eq (ab_ex x) (ab_ex y))
       (I.Prosa_Implementation_Definitions_ArrivalBound_instDecidableEqTask_arrivals_bound (ab_ex x) (ab_ex y))).
Proof. exact (rf_decide_ex _ _ _ (rf_eqtype_rel ab_ex ab_im rf_ab_rt x y)). Qed.

Definition rtab_bw (xL : IAB) (x'L : ITab IN) (H : IRtab xL x'L) : Rab.Rtask_ab (ab_im xL) (tabT_im Ni x'L) :=
  to_source _ _ (Rtask_ab_correspondence _ _ _ _ (rf_refl _) (rf_refl _))
    (rf_tr2 IRtab (rf_sym _ _ (rf_ab_rtL xL)) (rf_sym _ _ (rf_tabT_rtL Ne_ Ni rf_Ne_Ni x'L)) H).
Definition rtab_fw (x : AB.task_arrivals_bound) (x' : @Rab.task_arrivals_bound_T N) (H : Rab.Rtask_ab x x') :
    IRtab (ab_ex x) (tabT_ex Ne_ x') :=
  to_target _ _ (Rtask_ab_correspondence _ _ _ _ (rf_refl _) (rf_refl _)) H.