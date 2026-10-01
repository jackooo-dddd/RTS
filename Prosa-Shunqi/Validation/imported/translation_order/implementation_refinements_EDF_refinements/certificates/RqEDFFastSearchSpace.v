(* Re-bound copy of the accepted certificates/implementation_refinements_EDF_fast_search_space/RefEDFFastSearchSpaceCorrespondence.v: modules renamed (ImportedRefEDFFastSearchSpace=ImportedRefEDFRefinements,ReBase=RqBase,ReArrivalBound=RqArrivalBound,ReTask=RqTask,ReArrivalCurve=RqArrivalCurve,ReArrivalCurvePrefix=RqArrivalCurvePrefix,ReFastSearchSpaceComputation=RqFastSearchSpaceComputation), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(** Correspondences for [implementation/refinements/EDF/fast_search_space.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (the module with the
    recorded rewrite-order flag).  The base maps, definition correspondences and statement combinators are those of
    the accepted refinements.v, arrival_bound.v, task.v, arrival_curve.v, arrival_curve_prefix.v and
    fast_search_space_computation.v certificates, re-bound in [RqBase] … [RqFastSearchSpaceComputation].  Here:
    - the generic components of the accepted FP/fast_search_space.v certificate (element-mapped filtered sum and
      maximum, Boolean negation, [maxn]) are restated (same proofs), with [minn] against Lean's [min];
    - each of the file's twelve definitions is related to its translation for related inputs (tasks by [TaskRel], the
      file's own [Task]/[Job] aliases by their principal totals, task lists and numbers by the canonical maps, pairs
      componentwise), with the accepted [blocking_relevant] and EDF [is_in_search_space] unfolded on both sides;
    - the two statements are related by [PropSPropRel], composed from the accepted combinators.
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.EDF.fast_search_space.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFRefinements ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RqBase
  RqArrivalBound RqTask RqArrivalCurve RqArrivalCurvePrefix RqFastSearchSpaceComputation.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefEDFRefinements.
Module Efs := prosa.implementation.refinements.EDF.fast_search_space.
Module Rac := prosa.implementation.refinements.arrival_curve.
Module Rt := prosa.implementation.refinements.task.
Module Dt := prosa.implementation.definitions.task.

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

Lemma rf_eqnL a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL -> PropSPropRel (is_true (a == b)) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_eqn_rel a b). Qed.

(** MathComp [minn] against Lean's [min] on [Nat] ([minOfLe]: an [ite] on [≤]). *)
Lemma rf_minL_ex a b : Lean.eq (ne (minn a b)) (I.Min_min_inst1 LN I.instMinNat (ne a) (ne b)).
Proof.
  have E : minn a b = (if leq a b then a else b) by case: leqP.
  rewrite E.
  refine (rf_trans _ _ _ _ (rf_ite_ex (leq a b) _ (I.Nat_decLe (ne a) (ne b)) (ne a) (ne b)
    (rf_le_rel a _ b _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b)))).
  destruct (leq a b); exact (rf_refl _).
Qed.

Lemma rf_le_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL ->
  Lean.eq (be (leq a b)) (I.Decidable_decide (rf_le aL bL) (I.Nat_decLe aL bL)).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_le_decide_ex a b). Qed.

Lemma rf_add_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL -> Lean.eq (ne (a + b)) (rf_add aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_add_ex a b). Qed.

Lemma rf_sub_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL -> Lean.eq (ne (a - b)) (rf_sub aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_sub_ex a b). Qed.

Abbreviation IEbotw := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_bound_on_total_hep_workload.
Abbreviation IEcpFP := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_check_point_FP.
Abbreviation IEbb := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_blocking_bound_NP.
Abbreviation IEcpNP := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_check_point_NP.
Abbreviation IETask := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task.
Abbreviation IEJob := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_Job.
Abbreviation IEcss := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_correct_search_space.
Abbreviation IEssh := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_FP_h.
Abbreviation IEss := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_FP.
Abbreviation IEtssh := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF_h.
Abbreviation IEtss := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF.
Abbreviation IEssE := I.Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_EDF.

(** ** The file's own [Task] and [Job] aliases *)
Definition ETaskRel (t : Efs.Task) (tL : IETask) : SProp := Lean.eq (task_ex t) tL.
Definition EJobRel (j : Efs.Job) (jL : IEJob) : SProp := Lean.eq (job_ex j) jL.
Lemma Task_source_total (t : Efs.Task) : ETaskRel t (task_ex t). Proof. exact (rf_refl _). Qed.
Lemma Task_target_total (tL : IETask) : ETaskRel (task_im tL : Efs.Task) tL. Proof. exact (rf_task_rtL tL). Qed.
Lemma Job_source_total (j : Efs.Job) : EJobRel j (job_ex j). Proof. exact (rf_refl _). Qed.
Lemma Job_target_total (jL : IEJob) : EJobRel (job_im jL : Efs.Job) jL. Proof. exact (rf_job_rtL jL). Qed.

(** ** Arithmetic components *)
Lemma rf_rbf_ex t d : Lean.eq (ne (Rac.task_rbf t d)) (IAC_task_rbf (task_ex t) (ne d)).
Proof. exact (task_rbf_correspondence t _ d _ (rf_refl _) (rf_refl _)). Qed.

Lemma rf_rbf_rel_ex t d dL : Lean.eq (ne d) dL -> Lean.eq (ne (Rac.task_rbf t d)) (IAC_task_rbf (task_ex t) dL).
Proof. intro H. destruct H. exact (rf_rbf_ex t d). Qed.

Lemma rf_lt_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL ->
  Lean.eq (be (ltn a b)) (I.Decidable_decide (rf_lt aL bL) (I.Nat_decLt aL bL)).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_lt_decide_ex a b). Qed.

Lemma rf_min_rel_ex a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL ->
  Lean.eq (ne (minn a b)) (I.Min_min_inst1 LN I.instMinNat aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (rf_minL_ex a b). Qed.

(** [\cat_(x <- xs) F x] against the accepted [bigCatSeqAll]. *)
Lemma rf_bigcat_ex {X Y : Type} (e : X -> Y) (F : X -> seq nat) (FL : Y -> IList LN)
    (HF : forall x, Lean.eq (lex ne (F x)) (FL (e x))) xs :
  Lean.eq (lex ne (\cat_(x <- xs) F x)) (I.List_flatMap_inst3 Y LN FL (lex e xs)).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil. exact (rf_refl _).
  - rewrite big_cons.
    exact (rf_trans _ _ _ (rf_cat_ex ne _ _) (rf_congr2 (I.List_append_inst1 LN) _ _ _ _ (HF x) IH)).
Qed.

Lemma rf_or_ex a b : Lean.eq (be (a || b)) (I.Bool_or (be a) (be b)).
Proof. destruct a; destruct b; exact (rf_refl _). Qed.

Lemma rf_neq_task_ex (t1 t2 : Rt.Task) :
  PropSPropRel (is_true (t1 != t2)) (I.Not (Lean.eq (task_ex t1) (task_ex t2))).
Proof. exact (rf_negb_rel _ _ (rf_eqtype_rel task_ex task_im rf_task_rt t1 t2)). Qed.

(** ** The twelve definitions *)
Lemma rf_botw_ex ts t A d :
  Lean.eq (ne (Efs.bound_on_total_hep_workload ts t A d)) (IEbotw (lex task_ex ts) (task_ex t) (ne A) (ne d)).
Proof.
  unfold Efs.bound_on_total_hep_workload.
  refine (rf_sumFilteredE_ex task_ex _ _ _ _ _ _ ts).
  - intro o. exact (rf_decide_ex _ _ _ (rf_neq_task_ex o t)).
  - intro o. refine (rf_rbf_rel_ex _ _ _ (rf_min_rel_ex _ _ _ _ _ (rf_refl _))).
    exact (rf_sub_rel_ex _ _ _ _ (rf_add_rel_ex _ _ _ _ (rf_add_ex A (S O)) (rf_refl _)) (rf_refl _)).
Qed.

Lemma bound_on_total_hep_workload_correspondence tsR tsL tR tL AR AL dR dL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne AR) AL -> Lean.eq (ne dR) dL ->
  Lean.eq (ne (Efs.bound_on_total_hep_workload tsR tR AR dR)) (IEbotw tsL tL AL dL).
Proof. intros Hs Ht HA Hd. destruct Hs. destruct Ht. destruct HA. destruct Hd. exact (rf_botw_ex tsR tR AR dR). Qed.

Lemma rf_cpFP_ex ts t R p :
  Lean.eq (be (Efs.check_point_FP ts t R p)) (IEcpFP (lex task_ex ts) (task_ex t) (ne R) (pre ne ne p)).
Proof.
  destruct p as [a f]. unfold Efs.check_point_FP. cbn [fst snd].
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_le_decide_ex f R))).
  refine (rf_le_rel_ex _ _ _ _ _ (rf_add_ex a f)).
  refine (rf_add_rel_ex _ _ _ _ _ _).
  - exact (rf_rbf_rel_ex _ _ _ (rf_add_ex a (S O))).
  - exact (rf_trans _ _ _ (rf_botw_ex ts t a (a + f)) (rf_congr (IEbotw _ _ _) _ _ (rf_add_ex a f))).
Qed.

Lemma check_point_FP_correspondence tsR tsL tR tL RR RL pR pL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne RR) RL -> Lean.eq (pre ne ne pR) pL ->
  Lean.eq (be (Efs.check_point_FP tsR tR RR pR)) (IEcpFP tsL tL RL pL).
Proof. intros Hs Ht HR Hp. destruct Hs. destruct Ht. destruct HR. destruct Hp. exact (rf_cpFP_ex tsR tR RR pR). Qed.

Lemma rf_bb_ex ts t A : Lean.eq (ne (Efs.blocking_bound_NP ts t A)) (IEbb (lex task_ex ts) (task_ex t) (ne A)).
Proof.
  unfold Efs.blocking_bound_NP.
  have Hm := rf_map_ex task_ex task_ex (fun i : Rt.Task => i) (fun i : ITask => i) (fun a => rf_refl _) ts.
  refine (rf_trans _ _ _ (rf_maxFilteredE_ex task_ex _ _ _ _ _ _ _)
    (rf_congr (fun l => I.Prosa_Util_Sum_maxFiltered_inst1 ITask l _ _) _ _ Hm)).
  - intro o. refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
    + refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
      * exact (rf_lt_rel_ex _ _ _ _ (rf_refl _) (rf_cma_ex o (S O))).
      * exact (rf_lt_decide_ex O (Dt.task_cost o)).
    + exact (rf_lt_rel_ex _ _ _ _ (rf_add_ex _ _) (rf_refl _)).
  - intro o. exact (rf_sub_ex (Dt.task_cost o) (S O)).
Qed.

Lemma blocking_bound_NP_correspondence tsR tsL tR tL AR AL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne AR) AL ->
  Lean.eq (ne (Efs.blocking_bound_NP tsR tR AR)) (IEbb tsL tL AL).
Proof. intros Hs Ht HA. destruct Hs. destruct Ht. destruct HA. exact (rf_bb_ex tsR tR AR). Qed.

Lemma rf_cpNP_ex ts t R p :
  Lean.eq (be (Efs.check_point_NP ts t R p)) (IEcpNP (lex task_ex ts) (task_ex t) (ne R) (pre ne ne p)).
Proof.
  destruct p as [a f]. unfold Efs.check_point_NP. cbn [fst snd].
  have Hc1 := rf_sub_ex (Dt.task_cost t) (S O).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
  - refine (rf_le_rel_ex _ _ _ _ _ (rf_add_ex a f)).
    refine (rf_add_rel_ex _ _ _ _ _ _).
    + refine (rf_add_rel_ex _ _ _ _ (rf_bb_ex ts t a) _).
      exact (rf_sub_rel_ex _ _ _ _ (rf_rbf_rel_ex _ _ _ (rf_add_ex a (S O))) Hc1).
    + exact (rf_trans _ _ _ (rf_botw_ex ts t a (a + f)) (rf_congr (IEbotw _ _ _) _ _ (rf_add_ex a f))).
  - exact (rf_le_rel_ex _ _ _ _ (rf_add_rel_ex _ _ _ _ (rf_refl _) Hc1) (rf_refl _)).
Qed.

Lemma check_point_NP_correspondence tsR tsL tR tL RR RL pR pL :
  Lean.eq (lex task_ex tsR) tsL -> TaskRel tR tL -> Lean.eq (ne RR) RL -> Lean.eq (pre ne ne pR) pL ->
  Lean.eq (be (Efs.check_point_NP tsR tR RR pR)) (IEcpNP tsL tL RL pL).
Proof. intros Hs Ht HR Hp. destruct Hs. destruct Ht. destruct HR. destruct Hp. exact (rf_cpNP_ex tsR tR RR pR). Qed.

Lemma rf_rbf_neq_ex t x y xL yL : Lean.eq (ne x) xL -> Lean.eq (ne y) yL ->
  PropSPropRel (is_true (Rac.task_rbf t x != Rac.task_rbf t y))
    (I.Not (Lean.eq (IAC_task_rbf (task_ex t) xL) (IAC_task_rbf (task_ex t) yL))).
Proof. intros Hx Hy. exact (rf_negb_rel _ _ (rf_eqnL _ _ _ _ (rf_rbf_rel_ex t x xL Hx) (rf_rbf_rel_ex t y yL Hy))). Qed.

Lemma rf_iss_ex ts t L A :
  Lean.eq (be (prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space ts t L A))
    (I.Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space_inst1 ITask
       I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
       I.Prosa_Implementation_Definitions_Task_TaskCost I.Prosa_Implementation_Definitions_Task_TaskDeadline
       (lex task_ex ts) I.Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals (task_ex t) (ne L) (ne A)).
Proof.
  unfold prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space,
    prosa.results.rta.ideal.edf.bounded_pi.task_rbf_changes_at,
    prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at. cbv zeta.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_lt_decide_ex A L) _)).
  refine (rf_trans _ _ _ (rf_or_ex _ _) (rf_congr2 I.Bool_or _ _ _ _ _ _)).
  - exact (rf_decide_ex _ _ _ (rf_rbf_neq_ex t _ _ _ _ (rf_refl _) (rf_add_ex A (S O)))).
  - refine (rf_has_ex task_ex _ _ _ ts). intro o.
    refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _
      (rf_decide_ex _ _ _ (rf_neq_task_ex t o)) _)).
    exact (rf_decide_ex _ _ _ (rf_rbf_neq_ex o _ _ _ _
      (rf_sub_rel_ex _ _ _ _ (rf_add_ex _ _) (rf_refl _))
      (rf_sub_rel_ex _ _ _ _ (rf_add_rel_ex _ _ _ _ (rf_add_ex A (S O)) (rf_refl _)) (rf_refl _)))).
Qed.

Lemma rf_css_ex ts t L : Lean.eq (lex ne (Efs.correct_search_space ts t L)) (IEcss (lex task_ex ts) (task_ex t) (ne L)).
Proof.
  unfold Efs.correct_search_space.
  refine (rf_trans _ _ _ (rf_filter_ex ne _ _ (fun A => rf_iss_ex ts t L A) _) _).
  exact (rf_congr (I.List_filter_inst1 LN _) _ _ (rf_iota_ex O L)).
Qed.

Lemma correct_search_space_correspondence tsR tsL tR tL LR LL :
  Lean.eq (lex task_ex tsR) tsL -> ETaskRel tR tL -> Lean.eq (ne LR) LL ->
  Lean.eq (lex ne (Efs.correct_search_space tsR tR LR)) (IEcss tsL tL LL).
Proof. intros Hs Ht HL. destruct Hs. destruct Ht. destruct HL. exact (rf_css_ex tsR tR LR). Qed.

Lemma rf_offsets_ex t l r :
  Lean.eq (lex ne [seq Rac.get_horizon_of_task t * i | i <- iota l r])
    (I.List_map_inst3 LN LN (fun x => rf_mul (IAC_get_horizon_of_task (task_ex t)) x) (I.List_range' (ne l) (ne r) (ne (S O)))).
Proof.
  refine (rf_trans _ _ _ (rf_map_ex ne ne _ (fun x => rf_mul (IAC_get_horizon_of_task (task_ex t)) x)
    (fun a => rf_trans _ _ _ (rf_mul_ex _ a) (rf_congr (fun z => rf_mul z (ne a)) _ _ (rf_ghot_ex t))) _) _).
  exact (rf_congr (I.List_map_inst3 LN LN _) _ _ (rf_iota_ex l r)).
Qed.

Lemma rf_essh_ex t l r : Lean.eq (lex ne (Efs.search_space_emax_FP_h t l r)) (IEssh (task_ex t) (ne l) (ne r)).
Proof.
  unfold Efs.search_space_emax_FP_h. cbv zeta.
  refine (rf_trans _ _ _ (rf_map_ex ne ne predn I.Nat_pred rf_pred_ex _) _).
  refine (rf_congr (I.List_map_inst3 LN LN I.Nat_pred) _ _ _).
  refine (rf_trans _ _ _ (repeat_steps_with_offset_correspondence t _ _ _ (rf_refl _) (rf_refl _)) _).
  exact (rf_congr (IAC_repeat_steps_with_offset (task_ex t)) _ _ (rf_offsets_ex t l r)).
Qed.

Lemma search_space_emax_FP_h_correspondence tR tL lR lL rR rL :
  ETaskRel tR tL -> Lean.eq (ne lR) lL -> Lean.eq (ne rR) rL ->
  Lean.eq (lex ne (Efs.search_space_emax_FP_h tR lR rR)) (IEssh tL lL rL).
Proof. intros Ht Hl Hr. destruct Ht. destruct Hl. destruct Hr. exact (rf_essh_ex tR lR rR). Qed.

Lemma rf_ess_ex L t : Lean.eq (lex ne (Efs.search_space_emax_FP L t)) (IEss (ne L) (task_ex t)).
Proof.
  unfold Efs.search_space_emax_FP. cbv zeta.
  exact (rf_trans _ _ _ (rf_essh_ex t O _) (rf_congr (IEssh (task_ex t) (ne O)) _ _ (rf_bound_ex t L))).
Qed.

Lemma search_space_emax_FP_correspondence LR LL tR tL :
  Lean.eq (ne LR) LL -> ETaskRel tR tL -> Lean.eq (lex ne (Efs.search_space_emax_FP LR tR)) (IEss LL tL).
Proof. intros HL Ht. destruct HL. destruct Ht. exact (rf_ess_ex LR tR). Qed.

Lemma rf_etssh_ex t o l r :
  Lean.eq (lex ne (Efs.task_search_space_emax_EDF_h t o l r)) (IEtssh (task_ex t) (task_ex o) (ne l) (ne r)).
Proof.
  unfold Efs.task_search_space_emax_EDF_h. cbv zeta.
  refine (rf_trans _ _ _ (rf_map_ex ne ne predn I.Nat_pred rf_pred_ex _) _).
  refine (rf_congr (I.List_map_inst3 LN LN I.Nat_pred) _ _ _).
  refine (rf_trans _ _ _ (rf_spn_ex _ _) (rf_congr (fun l => I.Prosa_Util_List_shift_points_neg l _) _ _ _)).
  refine (rf_trans _ _ _ (rf_spp_ex _ _) (rf_congr (fun l => I.Prosa_Util_List_shift_points_pos l _) _ _ _)).
  refine (rf_trans _ _ _ (repeat_steps_with_offset_correspondence o _ _ _ (rf_refl _) (rf_refl _)) _).
  exact (rf_congr (IAC_repeat_steps_with_offset (task_ex o)) _ _ (rf_offsets_ex o l r)).
Qed.

Lemma task_search_space_emax_EDF_h_correspondence tR tL oR oL lR lL rR rL :
  ETaskRel tR tL -> ETaskRel oR oL -> Lean.eq (ne lR) lL -> Lean.eq (ne rR) rL ->
  Lean.eq (lex ne (Efs.task_search_space_emax_EDF_h tR oR lR rR)) (IEtssh tL oL lL rL).
Proof. intros Ht Ho Hl Hr. destruct Ht. destruct Ho. destruct Hl. destruct Hr. exact (rf_etssh_ex tR oR lR rR). Qed.

Lemma rf_ebound_ex t o L :
  Lean.eq (ne ((L + (Dt.task_deadline t - Dt.task_deadline o)) %/ Rac.get_horizon_of_task o).+1)
    (rf_add (rf_div (rf_add (ne L) (rf_sub (ne (Dt.task_deadline t)) (ne (Dt.task_deadline o))))
       (IAC_get_horizon_of_task (task_ex o))) (ne (S O))).
Proof.
  rewrite -addn1.
  refine (rf_add_rel_ex _ _ _ _ _ (rf_refl _)).
  refine (rf_trans _ _ _ (rf_div_ex _ _) (rf_congr2 rf_div _ _ _ _ _ (rf_ghot_ex o))).
  exact (rf_add_rel_ex _ _ _ _ (rf_refl _) (rf_sub_ex _ _)).
Qed.

Lemma rf_etss_ex t o L : Lean.eq (lex ne (Efs.task_search_space_emax_EDF t o L)) (IEtss (task_ex t) (task_ex o) (ne L)).
Proof.
  unfold Efs.task_search_space_emax_EDF. cbv zeta.
  exact (rf_trans _ _ _ (rf_etssh_ex t o O _) (rf_congr (IEtssh (task_ex t) (task_ex o) (ne O)) _ _ (rf_ebound_ex t o L))).
Qed.

Lemma task_search_space_emax_EDF_correspondence tR tL oR oL LR LL :
  ETaskRel tR tL -> ETaskRel oR oL -> Lean.eq (ne LR) LL ->
  Lean.eq (lex ne (Efs.task_search_space_emax_EDF tR oR LR)) (IEtss tL oL LL).
Proof. intros Ht Ho HL. destruct Ht. destruct Ho. destruct HL. exact (rf_etss_ex tR oR LR). Qed.

Lemma rf_essE_ex ts t L : Lean.eq (lex ne (Efs.search_space_emax_EDF ts t L)) (IEssE (lex task_ex ts) (task_ex t) (ne L)).
Proof.
  unfold Efs.search_space_emax_EDF.
  exact (rf_bigcat_ex task_ex _ _ (fun o => rf_etss_ex t o L) ts).
Qed.

Lemma search_space_emax_EDF_correspondence tsR tsL tR tL LR LL :
  Lean.eq (lex task_ex tsR) tsL -> ETaskRel tR tL -> Lean.eq (ne LR) LL ->
  Lean.eq (lex ne (Efs.search_space_emax_EDF tsR tR LR)) (IEssE tsL tL LL).
Proof. intros Hs Ht HL. destruct Hs. destruct Ht. destruct HL. exact (rf_essE_ex tsR tR LR). Qed.

(** ** The two statements *)
Lemma rf_list_eq_rel xs ys xsL ysL : Lean.eq (lex ne xs) xsL -> Lean.eq (lex ne ys) ysL ->
  PropSPropRel (Logic.eq xs ys) (Lean.eq xsL ysL).
Proof.
  intros Hx Hy. destruct Hx. destruct Hy. exact (rf_inj_rel (lex ne) (lim ni) (rf_lim_lex ne ni rf_ni_ne) xs ys).
Qed.