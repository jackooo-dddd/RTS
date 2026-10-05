(** Correspondences for [implementation/refinements/FP/fast_search_space.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (unchanged).  The
    base maps, definition correspondences and statement combinators are those of the accepted refinements.v,
    arrival_bound.v, task.v, arrival_curve.v, arrival_curve_prefix.v and fast_search_space_computation.v certificates,
    re-bound in [RfpBase] … [RfpFastSearchSpaceComputation].  Here:
    - the filtered sum and maximum over a task list are related through the task map (the accepted identity-carrier
      lemmas generalised to an element map, with the same proofs);
    - each of the file's nine definitions is related to its translation for related inputs (tasks by [TaskRel], task
      lists and numbers by the canonical maps, pairs componentwise), with the fixed-priority policy
      [NumericFPAscending] and the accepted [is_in_search_space] unfolded on both sides;
    - [search_space_subset_FP] is related by [PropSPropRel], composed from the accepted combinators.
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.FP.fast_search_space.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefFPFastSearchSpace ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RfpBase
  RfpArrivalBound RfpTask RfpArrivalCurve RfpArrivalCurvePrefix RfpFastSearchSpaceComputation.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefFPFastSearchSpace.
Module Ffs := prosa.implementation.refinements.FP.fast_search_space.
Module Rac := prosa.implementation.refinements.arrival_curve.
Module Rt := prosa.implementation.refinements.task.
Module Dt := prosa.implementation.definitions.task.


Abbreviation IFohep := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_ohep_task.
Abbreviation IFthep := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_total_hep_rbf.
Abbreviation IFtohep := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_total_ohep_rbf.
Abbreviation IFcpFP := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_check_point_FP.
Abbreviation IFbb := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_blocking_bound_NP.
Abbreviation IFcpNP := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_check_point_NP.
Abbreviation IFcss := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_correct_search_space.
Abbreviation IFssh := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP_h.
Abbreviation IFss := I.Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP.
Abbreviation ITask := I.Prosa_Implementation_Refinements_Task_Task.

(** ** Generic components *)

(** Negation of a related Boolean. *)
Lemma rf_negb_rel (b : bool) (Q : SProp) :
  PropSPropRel (is_true b) Q -> PropSPropRel (is_true (~~ b)) (I.Not Q).
Proof.
  intro R. apply prop_sprop_rel_intro.
  - intros hn q. have h := sprop_to_prop _ _ R q. rewrite h in hn. exact (match Bool.diff_false_true hn with end).
  - intro hn. destruct b eqn:E.
    + exact (rf_false_elim _ (hn (prop_to_sprop _ _ R Logic.eq_refl))).
    + apply strictly_inhabits. exact Logic.eq_refl.
Qed.

(** The accepted filtered sum and maximum, generalised to an element map (same proofs). *)
Lemma rf_sumFilteredE_ex {X Y : Type} (e : X -> Y) (P : X -> bool) (PL : Y -> I.Bool) (F : X -> nat) (FL : Y -> LN)
    (HP : forall x, Lean.eq (be (P x)) (PL (e x))) (HF : forall x, Lean.eq (ne (F x)) (FL (e x))) xs :
  Lean.eq (ne (\sum_(x <- xs | P x) F x)) (I.Prosa_Util_Sum_sumFiltered_inst1 Y (lex e xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil. exact (rf_refl _).
  - rewrite big_cons.
    change (Lean.eq (ne (if P x then F x + \sum_(j <- xs | P j) F j else \sum_(j <- xs | P j) F j))
      (I.List_sum_inst1 LN I.instAddNat (I.MulZeroClass_toZero_inst1 LN I.Nat_instMulZeroClass)
        (I.List_map_inst3 Y LN FL
          (I.Bool_casesOn (fun _ => IList Y) (PL (e x)) (I.List_filter_inst1 Y PL (lex e xs))
             (Icons Y (e x) (I.List_filter_inst1 Y PL (lex e xs))))))).
    have Hx := HP x. rf_rw Hx.
    destruct (P x); cbn [be].
    + exact (rf_trans _ _ _ (rf_add_ex _ _) (rf_congr2 sub_imported_add _ _ _ _ (HF x) IH)).
    + exact IH.
Qed.

(** MathComp [maxn] against Lean's [max] on [Nat] ([maxOfLe]: an [ite] on [≤]). *)
Lemma rf_maxL_ex a b : Lean.eq (ne (maxn a b)) (I.Max_max_inst1 LN I.Nat_instMax (ne a) (ne b)).
Proof.
  have E : maxn a b = (if leq a b then b else a).
  { by case: leqP. }
  rewrite E.
  refine (rf_trans _ _ _ _ (rf_ite_ex (leq a b) _ (I.Nat_decLe (ne a) (ne b)) (ne b) (ne a)
    (rf_le_rel a _ b _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b)))).
  destruct (leq a b); exact (rf_refl _).
Qed.

Lemma rf_maxFilteredE_ex {X Y : Type} (e : X -> Y) (P : X -> bool) (PL : Y -> I.Bool) (F : X -> nat) (FL : Y -> LN)
    (HP : forall x, Lean.eq (be (P x)) (PL (e x))) (HF : forall x, Lean.eq (ne (F x)) (FL (e x))) xs :
  Lean.eq (ne (\max_(x <- xs | P x) F x)) (I.Prosa_Util_Sum_maxFiltered_inst1 Y (lex e xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil. exact (rf_refl _).
  - rewrite big_cons.
    change (Lean.eq (ne (if P x then maxn (F x) (\max_(j <- xs | P j) F j) else \max_(j <- xs | P j) F j))
      (I.List_foldr_inst3 LN LN (I.Max_max_inst1 LN I.Nat_instMax) (I.OfNat_ofNat_inst1 LN 0 (I.instOfNatNat 0))
        (I.List_map_inst3 Y LN FL
          (I.Bool_casesOn (fun _ => IList Y) (PL (e x)) (I.List_filter_inst1 Y PL (lex e xs))
             (Icons Y (e x) (I.List_filter_inst1 Y PL (lex e xs))))))).
    have Hx := HP x. rf_rw Hx.
    destruct (P x); cbn [be].
    + exact (rf_trans _ _ _ (rf_maxL_ex _ _) (rf_congr2 (I.Max_max_inst1 LN I.Nat_instMax) _ _ _ _ (HF x) IH)).
    + exact IH.
Qed.

Lemma rf_not_ex b : Lean.eq (be (~~ b)) (I.Bool_not (be b)).
Proof. destruct b; exact (rf_refl _). Qed.

Lemma rf_eqnL a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL -> PropSPropRel (is_true (a == b)) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_eqn_rel a b). Qed.

(** ** The imported fixed-priority policy and request-bound function at the concrete tasks *)
Abbreviation IDecT := I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task.
Abbreviation INFP := (I.Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1 ITask IDecT
  I.Prosa_Implementation_Definitions_Task_TaskPriority).
Definition IHep (a b : ITask) : I.Bool := I.Prosa_Model_Priority_Definitions_FP_policy_hep_task_inst1 ITask IDecT INFP a b.
Definition IRbf (a : ITask) (d : LN) : LN :=
  I.Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function_inst1 ITask IDecT
    I.Prosa_Implementation_Definitions_Task_TaskCost I.Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals a d.

Lemma rf_hep_ex t1 t2 :
  Lean.eq (be (leq (Dt.task_priority t2) (Dt.task_priority t1))) (IHep (task_ex t1) (task_ex t2)).
Proof. exact (rf_le_decide_ex _ _). Qed.

Lemma rf_rbf_ex t d : Lean.eq (ne (Rac.task_rbf t d)) (IRbf (task_ex t) (ne d)).
Proof. exact (task_rbf_correspondence t _ d _ (rf_refl _) (rf_refl _)). Qed.

(** ** The nine definitions *)
Lemma rf_ohep_ex t1 t2 : Lean.eq (be (Ffs.ohep_task t1 t2)) (IFohep (task_ex t1) (task_ex t2)).
Proof.
  unfold Ffs.ohep_task.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_hep_ex t1 t2) _)).
  exact (rf_decide_ex _ _ _ (rf_negb_rel _ _ (rf_eqtype_rel task_ex task_im rf_task_rt t1 t2))).
Qed.

Lemma ohep_task_correspondence t1R t1L t2R t2L :
  TaskRel t1R t1L -> TaskRel t2R t2L -> Lean.eq (be (Ffs.ohep_task t1R t2R)) (IFohep t1L t2L).
Proof. intros H1 H2. destruct H1. destruct H2. exact (rf_ohep_ex t1R t2R). Qed.

Lemma rf_thep_ex ts t d : Lean.eq (ne (Ffs.total_hep_rbf ts t d)) (IFthep (lex task_ex ts) (task_ex t) (ne d)).
Proof.
  exact (rf_sumFilteredE_ex task_ex _ (fun y => IHep y (task_ex t)) _ (fun y => IRbf y (ne d))
    (fun o => rf_hep_ex o t) (fun o => rf_rbf_ex o d) ts).
Qed.

Lemma total_hep_rbf_correspondence tsR tsL tR tL dR dL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne dR) dL ->
  Lean.eq (ne (Ffs.total_hep_rbf tsR tR dR)) (IFthep tsL tL dL).
Proof. intros Hs Ht Hd. destruct Hs. destruct Ht. destruct Hd. exact (rf_thep_ex tsR tR dR). Qed.

Lemma rf_tohep_ex ts t d : Lean.eq (ne (Ffs.total_ohep_rbf ts t d)) (IFtohep (lex task_ex ts) (task_ex t) (ne d)).
Proof.
  exact (rf_sumFilteredE_ex task_ex _ (fun y => IFohep y (task_ex t)) _ (fun y => IRbf y (ne d))
    (fun o => rf_ohep_ex o t) (fun o => rf_rbf_ex o d) ts).
Qed.

Lemma total_ohep_rbf_correspondence tsR tsL tR tL dR dL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne dR) dL ->
  Lean.eq (ne (Ffs.total_ohep_rbf tsR tR dR)) (IFtohep tsL tL dL).
Proof. intros Hs Ht Hd. destruct Hs. destruct Ht. destruct Hd. exact (rf_tohep_ex tsR tR dR). Qed.

Lemma rf_le_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL ->
  Lean.eq (be (leq a b)) (I.Decidable_decide (rf_le aL bL) (I.Nat_decLe aL bL)).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_le_decide_ex a b). Qed.

Lemma rf_add_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL -> Lean.eq (ne (a + b)) (rf_add aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_add_ex a b). Qed.

Lemma rf_sub_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL -> Lean.eq (ne (a - b)) (rf_sub aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_sub_ex a b). Qed.

Lemma rf_cpFP_ex ts t R p :
  Lean.eq (be (Ffs.check_point_FP ts t R p)) (IFcpFP (lex task_ex ts) (task_ex t) (ne R) (pre ne ne p)).
Proof.
  destruct p as [a f]. unfold Ffs.check_point_FP. cbn [fst snd].
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_le_decide_ex f R))).
  refine (rf_le_rel_ex _ _ _ _ _ (rf_add_ex a f)).
  refine (rf_add_rel_ex _ _ _ _ _ _).
  - exact (rf_trans _ _ _ (rf_rbf_ex t (a + 1)) (rf_congr (IRbf (task_ex t)) _ _ (rf_add_ex a 1))).
  - exact (rf_trans _ _ _ (rf_tohep_ex ts t (a + f)) (rf_congr (IFtohep _ _) _ _ (rf_add_ex a f))).
Qed.

Lemma check_point_FP_correspondence tsR tsL tR tL RR RL pR pL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne RR) RL -> Lean.eq (pre ne ne pR) pL ->
  Lean.eq (be (Ffs.check_point_FP tsR tR RR pR)) (IFcpFP tsL tL RL pL).
Proof. intros Hs Ht HR Hp. destruct Hs. destruct Ht. destruct HR. destruct Hp. exact (rf_cpFP_ex tsR tR RR pR). Qed.

Lemma rf_bb_ex ts t : Lean.eq (ne (Ffs.blocking_bound_NP ts t)) (IFbb (lex task_ex ts) (task_ex t)).
Proof.
  exact (rf_maxFilteredE_ex task_ex _ (fun y => I.Bool_not (IHep y (task_ex t))) _ _
    (fun o => rf_trans _ _ _ (rf_not_ex _) (rf_congr I.Bool_not _ _ (rf_hep_ex o t)))
    (fun o => rf_sub_ex (Dt.task_cost o) (S O)) ts).
Qed.

Lemma blocking_bound_NP_correspondence tsR tsL tR tL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne (Ffs.blocking_bound_NP tsR tR)) (IFbb tsL tL).
Proof. intros Hs Ht. destruct Hs. destruct Ht. exact (rf_bb_ex tsR tR). Qed.

Lemma rf_cpNP_ex ts t R p :
  Lean.eq (be (Ffs.check_point_NP ts t R p)) (IFcpNP (lex task_ex ts) (task_ex t) (ne R) (pre ne ne p)).
Proof.
  destruct p as [a f]. unfold Ffs.check_point_NP. cbn [fst snd].
  have Hc1 := rf_sub_ex (Dt.task_cost t) (S O).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
  - refine (rf_le_rel_ex _ _ _ _ _ (rf_add_ex a f)).
    refine (rf_add_rel_ex _ _ _ _ _ _).
    + refine (rf_add_rel_ex _ _ _ _ (rf_bb_ex ts t) _).
      refine (rf_sub_rel_ex _ _ _ _ _ Hc1).
      exact (rf_trans _ _ _ (rf_rbf_ex t (a + 1)) (rf_congr (IRbf (task_ex t)) _ _ (rf_add_ex a 1))).
    + exact (rf_trans _ _ _ (rf_tohep_ex ts t (a + f)) (rf_congr (IFtohep _ _) _ _ (rf_add_ex a f))).
  - exact (rf_le_rel_ex _ _ _ _ (rf_add_rel_ex _ _ _ _ (rf_refl _) Hc1) (rf_refl _)).
Qed.

Lemma check_point_NP_correspondence tsR tsL tR tL RR RL pR pL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne RR) RL -> Lean.eq (pre ne ne pR) pL ->
  Lean.eq (be (Ffs.check_point_NP tsR tR RR pR)) (IFcpNP tsL tL RL pL).
Proof. intros Hs Ht HR Hp. destruct Hs. destruct Ht. destruct HR. destruct Hp. exact (rf_cpNP_ex tsR tR RR pR). Qed.

Lemma rf_iss_ex t L A :
  Lean.eq (be (prosa.results.rta.ideal.fp.bounded_pi.is_in_search_space t L A))
    (I.Prosa_Results_Rta_Ideal_Fp_BoundedPi_is_in_search_space_inst1 ITask IDecT
       I.Prosa_Implementation_Definitions_Task_TaskCost I.Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
       (task_ex t) (ne L) (ne A)).
Proof.
  unfold prosa.results.rta.ideal.fp.bounded_pi.is_in_search_space. cbv zeta.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_lt_decide_ex A L) _)).
  exact (rf_decide_ex _ _ _ (rf_negb_rel _ _ (rf_eqnL _ _ _ _ (rf_rbf_ex t A)
    (rf_trans _ _ _ (rf_rbf_ex t (A + 1)) (rf_congr (IRbf (task_ex t)) _ _ (rf_add_ex A 1)))))).
Qed.

Lemma rf_css_ex t L : Lean.eq (lex ne (Ffs.correct_search_space t L)) (IFcss (task_ex t) (ne L)).
Proof.
  unfold Ffs.correct_search_space.
  refine (rf_trans _ _ _ (rf_filter_ex ne _ _ (fun A => rf_iss_ex t L A) _) _).
  exact (rf_congr (I.List_filter_inst1 LN _) _ _ (rf_iota_ex O L)).
Qed.

Lemma correct_search_space_correspondence tR tL LR LL :
  TaskRel tR tL -> Lean.eq (ne LR) LL -> Lean.eq (lex ne (Ffs.correct_search_space tR LR)) (IFcss tL LL).
Proof. intros Ht HL. destruct Ht. destruct HL. exact (rf_css_ex tR LR). Qed.

Lemma rf_fssh_ex t l r : Lean.eq (lex ne (Ffs.search_space_emax_FP_h t l r)) (IFssh (task_ex t) (ne l) (ne r)).
Proof.
  unfold Ffs.search_space_emax_FP_h. cbv zeta.
  refine (rf_trans _ _ _ (rf_map_ex ne ne predn I.Nat_pred rf_pred_ex _) _).
  refine (rf_congr (I.List_map_inst3 LN LN I.Nat_pred) _ _ _).
  refine (rf_trans _ _ _ (repeat_steps_with_offset_correspondence t _ _ _ (rf_refl _) (rf_refl _)) _).
  refine (rf_congr (IAC_repeat_steps_with_offset (task_ex t)) _ _ _).
  pose hL := IAC_get_horizon_of_task (task_ex t).
  refine (rf_trans _ _ _ (rf_map_ex ne ne (muln (Rac.get_horizon_of_task t)) (fun x => rf_mul hL x)
    (fun a => rf_trans _ _ _ (rf_mul_ex _ a) (rf_congr (fun z => rf_mul z (ne a)) _ _ (rf_ghot_ex t))) _) _).
  exact (rf_congr (I.List_map_inst3 LN LN (fun x => rf_mul hL x)) _ _ (rf_iota_ex l r)).
Qed.

Lemma search_space_emax_FP_h_correspondence tR tL lR lL rR rL :
  TaskRel tR tL -> Lean.eq (ne lR) lL -> Lean.eq (ne rR) rL ->
  Lean.eq (lex ne (Ffs.search_space_emax_FP_h tR lR rR)) (IFssh tL lL rL).
Proof. intros Ht Hl Hr. destruct Ht. destruct Hl. destruct Hr. exact (rf_fssh_ex tR lR rR). Qed.

Lemma rf_fss_ex t L : Lean.eq (lex ne (Ffs.search_space_emax_FP t L)) (IFss (task_ex t) (ne L)).
Proof.
  unfold Ffs.search_space_emax_FP. cbv zeta.
  exact (rf_trans _ _ _ (rf_fssh_ex t O _) (rf_congr (IFssh (task_ex t) (ne O)) _ _ (rf_bound_ex t L))).
Qed.

Lemma search_space_emax_FP_correspondence tR tL LR LL :
  TaskRel tR tL -> Lean.eq (ne LR) LL -> Lean.eq (lex ne (Ffs.search_space_emax_FP tR LR)) (IFss tL LL).
Proof. intros Ht HL. destruct Ht. destruct HL. exact (rf_fss_ex tR LR). Qed.

(** ** The statement *)
Definition rf_src_search_space_subset_FP := ltac:(src_ty Ffs.search_space_subset_FP).
Definition rf_tgt_search_space_subset_FP :=
  ltac:(src_ty I.Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_subset_FP).
Lemma search_space_subset_FP_correspondence : PropSPropRel rf_src_search_space_subset_FP rf_tgt_search_space_subset_FP.
Proof.
  apply rf_forall_nat. intro L. rfs_head ts tsk.
  apply rf_forall_nat. intro A.
  apply rf_imp_rel; first exact (rf_mem_via A _ _ (rf_css_ex tsk L)).
  exact (rf_mem_via A _ _ (rf_fss_ex tsk L)).
Qed.
