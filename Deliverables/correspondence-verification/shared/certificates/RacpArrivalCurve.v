(* Re-bound copy of the accepted certificates/implementation_refinements_arrival_curve/RefArrivalCurveCorrespondence.v: modules renamed (ImportedRefArrivalCurve=ImportedRefArrivalCurvePrefix,RacBase=RacpBase,RacArrivalBound=RacpArrivalBound,RacTask=RacpTask), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(** Correspondences for [implementation/refinements/arrival_curve.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (unchanged). The base
    maps and correspondences are those of the accepted refinements.v, arrival_bound.v and task.v certificates,
    re-bound in [RacpBase], [RacpArrivalBound] and [RacpTask]. Here:
    - each definition is related to its translation for related inputs (tasks by [TaskRel], numbers by the canonical
      map); the [Prop]-valued ones by [PropSPropRel];
    - [arrival_cases] by [PropSPropRel], and the eight refinement instances by [TypeCorrespondence].
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.arrival_curve.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefArrivalCurvePrefix ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RacpBase
  RacpArrivalBound RacpTask.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefArrivalCurvePrefix.
Module Rac := prosa.implementation.refinements.arrival_curve.
Module Rt := prosa.implementation.refinements.task.
Module Dt := prosa.implementation.definitions.task.
Module Rab := prosa.implementation.refinements.arrival_bound.
Module AB := prosa.implementation.definitions.arrival_bound.
Module EAC := prosa.implementation.definitions.extrapolated_arrival_curve.

(** ** Imported names *)
Abbreviation IGACP := I.Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix.
Abbreviation ICMA := I.Prosa_Implementation_Definitions_Task_concrete_max_arrivals.
Abbreviation IEhor := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of.
Abbreviation IEsteps := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of.
Abbreviation IEts := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of.
Abbreviation IEeac := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve.
Abbreviation IEvalue := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at.
Abbreviation IEpos := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon.
Abbreviation IElarge := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon.
Abbreviation IElarge_dec := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec.
Abbreviation IEnoinf := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals.
Abbreviation IEburst := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts.
Abbreviation IEsorted := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps.
Abbreviation IEvalid := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix.
Abbreviation IEvalid_dec := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec.
Abbreviation IEltn := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps.
Abbreviation IEsortedBool := I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1.

(** ** The arrival-curve prefix of a task *)
Lemma rf_gacp_ex t : Lean.eq (pfx ne (Dt.get_arrival_curve_prefix t)) (IGACP (task_ex t)).
Proof. destruct t as [i c a d p]. destruct a; exact (rf_refl _). Qed.

Lemma rf_horizon_ex p : Lean.eq (ne (EAC.horizon_of p)) (IEhor (pfx ne p)).
Proof. destruct p; exact (rf_refl _). Qed.

Lemma rf_cma_ex t d : Lean.eq (ne (Dt.concrete_max_arrivals t d)) (ICMA (task_ex t) (ne d)).
Proof.
  exact (rf_trans _ _ _ (rf_EAC_eac_ex _ d) (rf_congr (fun p => IEeac p (ne d)) _ _ (rf_gacp_ex t))).
Qed.

(** ** Transport of target propositions *)
Definition rf_trS {A B : Type} (P : A -> B -> SProp) {x y : A} {u v : B}
    (H : Lean.eq x y) (H' : Lean.eq u v) (p : P x u) : P y v :=
  match H in Lean.eq _ z return P z v with
  | Lean.eq_refl => match H' in Lean.eq _ w return P x w with Lean.eq_refl => p end
  end.

(** ** Membership (any [eqType] with a map and its left inverse) *)
Abbreviation IMem := I.List_Mem_inst1.

Lemma rf_mem_fw {A : eqType} {C : Type} (e : A -> C) (x : A) xs : is_true (x \in xs) -> IMem C (e x) (lex e xs).
Proof.
  induction xs as [|y ys IH]; intro H.
  - exact (match Bool.diff_false_true H with end).
  - destruct (@eqP A x y) as [Hxy|Hxy].
    + subst y. exact (I.List_Mem_head_inst1 C (e x) (lex e ys)).
    + have H' : is_true (x \in ys) by move: H; rewrite in_cons; move/eqP: Hxy => /negbTE ->.
      exact (I.List_Mem_tail_inst1 C (e x) (e y) (lex e ys) (IH H')).
Qed.

Lemma rf_mem_head {A : eqType} (x : A) ys : is_true (x \in x :: ys).
Proof. by rewrite in_cons eqxx. Qed.
Lemma rf_mem_tail {A : eqType} (x y : A) ys : is_true (x \in ys) -> is_true (x \in y :: ys).
Proof. by move=> h; rewrite in_cons h orbT. Qed.

Fixpoint rf_mem_bw {A : eqType} {C : Type} (e : A -> C) (i : C -> A) (Hi : forall a, i (e a) = a) (x : A)
    (L : IList C) (H : IMem C (e x) L) {struct H} : StrictlyInhabited (is_true (x \in lim i L)) :=
  match H in I.List_Mem_inst1 _ _ L' return StrictlyInhabited (is_true (x \in lim i L')) with
  | I.List_Mem_head_inst1 ys =>
      strictly_inhabits (eq_ind_r (fun z => is_true (x \in z :: lim i ys)) (rf_mem_head x (lim i ys)) (Hi x))
  | I.List_Mem_tail_inst1 y ys Ht =>
      match rf_mem_bw e i Hi x ys Ht with
      | strictly_inhabits h => strictly_inhabits (rf_mem_tail x (i y) (lim i ys) h)
      end
  end.

Lemma rf_mem_rel {A : eqType} {C : Type} (e : A -> C) (i : C -> A) (Hi : forall a, i (e a) = a) (x : A) xs :
  PropSPropRel (is_true (x \in xs)) (IMem C (e x) (lex e xs)).
Proof.
  apply prop_sprop_rel_intro.
  - exact (rf_mem_fw e x xs).
  - intro H. have h := rf_mem_bw e i Hi x _ H. by rewrite (rf_lim_lex e i Hi) in h.
Qed.

(** ** The validity of a prefix *)
Lemma rf_EAC_pos_ex p : Lean.eq (be (EAC.positive_horizon p)) (IEpos (pfx ne p)).
Proof. destruct p as [h st]. exact (rf_lt_decide_ex O h). Qed.

Lemma rf_EAC_large_dec_ex p : Lean.eq (be (EAC.large_horizon_dec p)) (IElarge_dec (pfx ne p)).
Proof.
  destruct p as [h st]. unfold EAC.large_horizon_dec.
  pose PL := fun s => I.Decidable_decide (rf_le s (ne h)) (I.Nat_decLe s (ne h)).
  refine (rf_trans _ _ _ (rf_all_ex ne _ PL (fun s => rf_le_decide_ex s h) _) _).
  exact (rf_congr (fun l => I.List_all_inst1 LN l PL) _ _ (rf_EAC_time_steps_ex (h, st))).
Qed.

Lemma rf_eqn_rel a b : PropSPropRel (is_true (a == b)) (Lean.eq (ne a) (ne b)).
Proof.
  have R := rf_eq_rel a (ne a) b (ne b) (sub_nat_rel_canonical a) (sub_nat_rel_canonical b).
  apply prop_sprop_rel_intro.
  - move/eqP => h. exact (prop_to_sprop _ _ R h).
  - intro h. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ R h).
Qed.

Lemma rf_EAC_noinf_ex p : Lean.eq (be (EAC.no_inf_arrivals p)) (IEnoinf (pfx ne p)).
Proof.
  unfold EAC.no_inf_arrivals.
  refine (rf_trans _ _ _ (rf_decide_ex _ _ (I.instDecidableEqNat _ _) (rf_eqn_rel _ O)) _).
  exact (rf_congr (fun v => I.Decidable_decide (Lean.eq v (ne O)) (I.instDecidableEqNat v (ne O))) _ _
    (rf_EAC_value_at_ex p O)).
Qed.

Lemma rf_EAC_burst_ex p : Lean.eq (be (EAC.specified_bursts p)) (IEburst (pfx ne p)).
Proof.
  unfold EAC.specified_bursts.
  pose D := fun l => I.List_instDecidableMemOfLawfulBEq_inst1 LN (I.instBEqOfDecidableEq_inst1 LN I.instDecidableEqNat)
    I.Nat_instLawfulBEq (ne (S O)) l.
  refine (rf_trans _ _ _ (rf_decide_ex _ (IMem LN (ne (S O)) (lex ne (EAC.time_steps_of p))) (D _)
    (rf_mem_rel ne ni rf_ni_ne (S O) _)) _).
  exact (rf_congr (fun l => I.Decidable_decide (IMem LN (ne (S O)) l) (D l)) _ _ (rf_EAC_time_steps_ex p)).
Qed.

Lemma rf_EAC_sorted_ex p : Lean.eq (be (EAC.sorted_ltn_steps p)) (IEsorted (pfx ne p)).
Proof. destruct p as [h st]. exact (rf_sorted_ex (pre ne ne) _ IEltn rf_EAC_ltn_steps_ex st). Qed.

Lemma rf_EAC_valid_dec_ex p : Lean.eq (be (EAC.valid_arrival_curve_prefix_dec p)) (IEvalid_dec (pfx ne p)).
Proof.
  unfold EAC.valid_arrival_curve_prefix_dec.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_EAC_sorted_ex p))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_EAC_burst_ex p))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (rf_EAC_noinf_ex p))).
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_EAC_pos_ex p) (rf_EAC_large_dec_ex p))).
Qed.

(** A Boolean and its image. *)
Lemma rf_true_rel (b : bool) bL : Lean.eq (be b) bL -> PropSPropRel (is_true b) (Lean.eq bL I.Bool_true).
Proof.
  intro H. destruct H. apply prop_sprop_rel_intro.
  - intro h. rewrite h. exact (rf_refl _).
  - intro h. apply strictly_inhabits. exact (rf_bool_of b h).
Qed.

Lemma rf_EAC_large_rel p : PropSPropRel (EAC.large_horizon p) (IElarge (pfx ne p)).
Proof.
  destruct p as [h st]. apply prop_sprop_rel_intro.
  - intros H sL hm.
    have hm' : IMem LN (ne (ni sL)) (lex ne (EAC.time_steps_of (h, st))) :=
      rf_trS (IMem LN) (rf_sym _ _ (rf_ne_ni sL)) (rf_sym _ _ (rf_EAC_time_steps_ex (h, st))) hm.
    destruct (rf_mem_bw ne ni rf_ni_ne (ni sL) _ hm') as [hin]. rewrite (rf_lim_lex ne ni rf_ni_ne) in hin.
    have hle := prop_to_sprop _ _ (rf_le_rel _ _ _ _ (sub_nat_rel_canonical (ni sL)) (sub_nat_rel_canonical h)) (H _ hin).
    exact (rf_trS rf_le (rf_ne_ni sL) (rf_refl _) hle).
  - intro HL. apply strictly_inhabits. intros s hin.
    have hm := rf_trS (IMem LN) (rf_refl _) (rf_EAC_time_steps_ex (h, st)) (rf_mem_fw ne s _ hin).
    exact (sprop_to_prop _ _ (rf_le_rel _ _ _ _ (sub_nat_rel_canonical s) (sub_nat_rel_canonical h)) (HL _ hm)).
Qed.

Lemma rf_EAC_valid_rel p : PropSPropRel (EAC.valid_arrival_curve_prefix p) (IEvalid (pfx ne p)).
Proof.
  have R1 := rf_true_rel _ _ (rf_EAC_pos_ex p).
  have R2 := rf_EAC_large_rel p.
  have R3 := rf_true_rel _ _ (rf_EAC_noinf_ex p).
  have R4 := rf_true_rel _ _ (rf_EAC_burst_ex p).
  have R5 := rf_true_rel _ _ (rf_EAC_sorted_ex p).
  apply prop_sprop_rel_intro.
  - intros [h1 [h2 [h3 [h4 h5]]]].
    exact (Lean.And_intro _ _ (prop_to_sprop _ _ R1 h1) (Lean.And_intro _ _ (prop_to_sprop _ _ R2 h2)
      (Lean.And_intro _ _ (prop_to_sprop _ _ R3 h3) (Lean.And_intro _ _ (prop_to_sprop _ _ R4 h4) (prop_to_sprop _ _ R5 h5))))).
  - intros [h1 [h2 [h3 [h4 h5]]]]. apply strictly_inhabits.
    exact (conj (sprop_to_prop _ _ R1 h1) (conj (sprop_to_prop _ _ R2 h2)
      (conj (sprop_to_prop _ _ R3 h3) (conj (sprop_to_prop _ _ R4 h4) (sprop_to_prop _ _ R5 h5))))).
Qed.

(** ** Definitions *)
Abbreviation IAC_get_horizon_of_task := I.Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task.
Abbreviation IAC_get_time_steps_of_task := I.Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task.
Abbreviation IAC_time_steps_with_offset := I.Prosa_Implementation_Refinements_ArrivalCurve_time_steps_with_offset.
Abbreviation IAC_repeat_steps_with_offset := I.Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset.
Abbreviation IAC_task_rbf := I.Prosa_Implementation_Refinements_ArrivalCurve_task_rbf.
Abbreviation IAC_valid_arrivals := I.Prosa_Implementation_Refinements_ArrivalCurve_valid_arrivals.

Lemma rf_ghot_ex t : Lean.eq (ne (Rac.get_horizon_of_task t)) (IAC_get_horizon_of_task (task_ex t)).
Proof. exact (rf_trans _ _ _ (rf_horizon_ex _) (rf_congr IEhor _ _ (rf_gacp_ex t))). Qed.

Lemma get_horizon_of_task_correspondence tR tL :
  TaskRel tR tL -> Lean.eq (ne (Rac.get_horizon_of_task tR)) (IAC_get_horizon_of_task tL).
Proof. intro H. destruct H. exact (rf_ghot_ex tR). Qed.

Lemma rf_gtst_ex t : Lean.eq (lex ne (Rac.get_time_steps_of_task t)) (IAC_get_time_steps_of_task (task_ex t)).
Proof. exact (rf_trans _ _ _ (rf_EAC_time_steps_ex _) (rf_congr IEts _ _ (rf_gacp_ex t))). Qed.

Lemma get_time_steps_of_task_correspondence tR tL :
  TaskRel tR tL -> Lean.eq (lex ne (Rac.get_time_steps_of_task tR)) (IAC_get_time_steps_of_task tL).
Proof. intro H. destruct H. exact (rf_gtst_ex tR). Qed.

Lemma rf_tswo_n_ex t d :
  Lean.eq (lex ne (Rac.time_steps_with_offset t d)) (IAC_time_steps_with_offset (task_ex t) (ne d)).
Proof.
  unfold Rac.time_steps_with_offset.
  refine (rf_trans _ _ _ (rf_map_ex ne ne _ (fun x => rf_add x (ne d)) (fun x => rf_add_ex x d) _) _).
  exact (rf_congr (I.List_map_inst3 LN LN (fun x => rf_add x (ne d))) _ _ (rf_gtst_ex t)).
Qed.

Lemma time_steps_with_offset_correspondence tR tL dR dL :
  TaskRel tR tL -> Lean.eq (ne dR) dL ->
  Lean.eq (lex ne (Rac.time_steps_with_offset tR dR)) (IAC_time_steps_with_offset tL dL).
Proof. intros Ht Hd. destruct Ht. destruct Hd. exact (rf_tswo_n_ex tR dR). Qed.

Lemma repeat_steps_with_offset_correspondence tR tL oR oL :
  TaskRel tR tL -> Lean.eq (lex ne oR) oL ->
  Lean.eq (lex ne (Rac.repeat_steps_with_offset tR oR)) (IAC_repeat_steps_with_offset tL oL).
Proof.
  intros Ht Ho. destruct Ht. destruct Ho. unfold Rac.repeat_steps_with_offset.
  refine (rf_trans _ _ _ (rf_flatten_ex ne _) _).
  refine (rf_congr (I.List_flatten_inst1 LN) _ _ _).
  exact (rf_map_ex ne (lex ne) _ _ (fun d => rf_tswo_n_ex tR d) _).
Qed.

Lemma task_rbf_correspondence tR tL dR dL :
  TaskRel tR tL -> Lean.eq (ne dR) dL -> Lean.eq (ne (Rac.task_rbf tR dR)) (IAC_task_rbf tL dL).
Proof.
  intros Ht Hd. destruct Ht. destruct Hd.
  exact (rf_trans _ _ _ (rf_mul_ex _ _) (rf_congr (rf_mul (ne (Dt.task_cost tR))) _ _ (rf_cma_ex tR dR))).
Qed.

Lemma rf_valid_arrivals_ex t : Lean.eq (be (Rac.valid_arrivals t)) (IAC_valid_arrivals (task_ex t)).
Proof.
  destruct t as [i c a d p]. unfold Rac.valid_arrivals. cbn.
  destruct a as [x|x|e]; cbn [ab_ex].
  - exact (rf_le_decide_ex (S O) x).
  - exact (rf_le_decide_ex (S O) x).
  - exact (rf_EAC_valid_dec_ex e).
Qed.

Lemma valid_arrivals_correspondence tR tL :
  TaskRel tR tL -> Lean.eq (be (Rac.valid_arrivals tR)) (IAC_valid_arrivals tL).
Proof. intro H. destruct H. exact (rf_valid_arrivals_ex tR). Qed.

(** [Prop]-valued definitions *)
Abbreviation IABPer := I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic.
Abbreviation IABSpo := I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic.
Abbreviation IABArr' := I.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix.
Abbreviation ICTarr := I.Prosa_Implementation_Definitions_Task_concrete_task_task_arrival.

Lemma rf_arr_eq_rel tR (x : AB.task_arrivals_bound) :
  PropSPropRel (Dt.task_arrival tR = x) (Lean.eq (ICTarr (task_ex tR)) (ab_ex x)).
Proof.
  apply prop_sprop_rel_intro.
  - intro h. rewrite -h. exact (rf_refl _).
  - intro h. apply strictly_inhabits.
    have h' := f_equal ab_im (rf_to_coq h). by rewrite !rf_ab_rt in h'.
Qed.

Lemma is_periodic_arrivals_correspondence tR tL :
  TaskRel tR tL -> PropSPropRel (Rac.is_periodic_arrivals tR) (I.Prosa_Implementation_Refinements_ArrivalCurve_is_periodic_arrivals tL).
Proof.
  intro H. destruct H. apply prop_sprop_rel_intro.
  - intros [p hp]. exact (I.Exists_intro _ _ (ne p) (prop_to_sprop _ _ (rf_arr_eq_rel tR (AB.Periodic p)) hp)).
  - intros [pL hp]. apply strictly_inhabits. exists (ni pL).
    apply (sprop_to_prop _ _ (rf_arr_eq_rel tR (AB.Periodic (ni pL)))).
    exact (rf_trS (fun a b => Lean.eq a b) (rf_refl (ICTarr (task_ex tR))) (rf_congr IABPer _ _ (rf_sym _ _ (rf_ne_ni pL))) hp).
Qed.

Lemma is_sporadic_arrivals_correspondence tR tL :
  TaskRel tR tL -> PropSPropRel (Rac.is_sporadic_arrivals tR) (I.Prosa_Implementation_Refinements_ArrivalCurve_is_sporadic_arrivals tL).
Proof.
  intro H. destruct H. apply prop_sprop_rel_intro.
  - intros [p hp]. exact (I.Exists_intro _ _ (ne p) (prop_to_sprop _ _ (rf_arr_eq_rel tR (AB.Sporadic p)) hp)).
  - intros [pL hp]. apply strictly_inhabits. exists (ni pL).
    apply (sprop_to_prop _ _ (rf_arr_eq_rel tR (AB.Sporadic (ni pL)))).
    exact (rf_trS (fun a b => Lean.eq a b) (rf_refl (ICTarr (task_ex tR))) (rf_congr IABSpo _ _ (rf_sym _ _ (rf_ne_ni pL))) hp).
Qed.

Lemma is_etamax_arrivals_correspondence tR tL :
  TaskRel tR tL -> PropSPropRel (Rac.is_etamax_arrivals tR) (I.Prosa_Implementation_Refinements_ArrivalCurve_is_etamax_arrivals tL).
Proof.
  intro H. destruct H. apply prop_sprop_rel_intro.
  - intros [e he]. exact (I.Exists_intro _ _ (pfx ne e) (prop_to_sprop _ _ (rf_arr_eq_rel tR (AB.ArrivalPrefix e)) he)).
  - intros [eL he]. apply strictly_inhabits. exists (pfxi ni eL).
    apply (sprop_to_prop _ _ (rf_arr_eq_rel tR (AB.ArrivalPrefix (pfxi ni eL)))).
    exact (rf_trS (fun a b => Lean.eq a b) (rf_refl (ICTarr (task_ex tR))) (rf_congr IABArr' _ _ (rf_sym _ _ (rf_pfx_n eL))) he).
Qed.

Lemma has_valid_arrival_curve_prefix_correspondence tR tL :
  TaskRel tR tL ->
  PropSPropRel (Rac.has_valid_arrival_curve_prefix tR)
    (I.Prosa_Implementation_Refinements_ArrivalCurve_has_valid_arrival_curve_prefix tL).
Proof.
  intro H. destruct H. apply prop_sprop_rel_intro.
  - intros [e [he hv]]. refine (I.Exists_intro _ _ (pfx ne e) (Lean.And_intro _ _ _ _)).
    + rewrite -he. exact (rf_sym _ _ (rf_gacp_ex tR)).
    + exact (prop_to_sprop _ _ (rf_EAC_valid_rel e) hv).
  - intros [eL [he hv]]. apply strictly_inhabits. exists (pfxi ni eL).
    have he' : Lean.eq (pfx ne (Dt.get_arrival_curve_prefix tR)) (pfx ne (pfxi ni eL)) :=
      rf_trans _ _ _ (rf_gacp_ex tR) (rf_trans _ _ _ he (rf_sym _ _ (rf_pfx_n eL))).
    split.
    + have h := f_equal (pfxi ni) (rf_to_coq he'). by rewrite !(rf_pfxi_pfx ne ni rf_ni_ne) in h.
    + apply (sprop_to_prop _ _ (rf_EAC_valid_rel (pfxi ni eL))).
      exact (rf_trS (fun (a : unit) b => IEvalid b) (rf_refl tt) (rf_sym _ _ (rf_pfx_n eL)) hv).
Qed.

Lemma task_set_with_valid_arrivals_correspondence tsR tsL :
  Lean.eq (lex task_ex tsR) tsL ->
  PropSPropRel (Rac.task_set_with_valid_arrivals tsR)
    (I.Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals tsL).
Proof.
  intro H. destruct H. apply prop_sprop_rel_intro.
  - intros h tL hm.
    have hm' : IMem ICT (task_ex (task_im tL)) (lex task_ex tsR) := rf_trS (IMem ICT) (rf_sym _ _ (rf_task_rtL tL)) (rf_refl _) hm.
    destruct (rf_mem_bw task_ex task_im rf_task_rt (task_im tL : Rt.Task) _ hm') as [hin].
    rewrite (rf_lim_lex task_ex task_im rf_task_rt) in hin.
    have hv := rf_valid_arrivals_ex (task_im tL).
    exact (rf_trS (fun a b => Lean.eq (IAC_valid_arrivals a) b) (rf_task_rtL tL) (rf_of_coq (f_equal be (h _ hin)))
      (rf_sym _ _ hv)).
  - intro HL. apply strictly_inhabits. intros t hin.
    have hv := rf_trans _ _ _ (rf_valid_arrivals_ex t) (HL _ (rf_mem_fw task_ex t _ hin)).
    exact (rf_bool_of _ hv).
Qed.

(** ** The generic definitions at the binary numbers *)
Abbreviation IN0 := I.Prosa_Implementation_Refinements_Refinements_zero_N.
Abbreviation IN1 := I.Prosa_Implementation_Refinements_Refinements_one_N.
Abbreviation INaddI := I.Prosa_Implementation_Refinements_Refinements_add_N.
Abbreviation INmulI := I.Prosa_Implementation_Refinements_Refinements_mul_N.
Abbreviation INdivI := I.Prosa_Implementation_Refinements_Refinements_div_N.
Abbreviation INmodI := I.Prosa_Implementation_Refinements_Refinements_mod_N.
Abbreviation INeqI := I.Prosa_Implementation_Refinements_Refinements_eq_N.
Abbreviation INleqI := I.Prosa_Implementation_Refinements_Refinements_leq_N.
Abbreviation INltI := I.Prosa_Implementation_Refinements_Refinements_lt_N.
Abbreviation IABhor := I.Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T.
Abbreviation IABts := I.Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T.
Abbreviation IABeac := I.Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T.
Abbreviation IABvalid := I.Prosa_Implementation_Refinements_ArrivalBound_valid_extrapolated_arrival_curve_T.
Abbreviation ITgeac := I.Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T.

Lemma rf_geacT_N_ex t : Lean.eq (pfx Ne_ (Rt.get_extrapolated_arrival_curve_T t)) (ITgeac IN IN1 (taskT_ex Ne_ t)).
Proof. destruct t as [i c a d p]. destruct a; exact (rf_refl _). Qed.

Lemma rf_horT_N_pfx q : Lean.eq (Ne_ (Rab.horizon_of_T q)) (IABhor IN (pfx Ne_ q)).
Proof. destruct q; exact (rf_refl _). Qed.

Lemma rf_ghotT_N_ex t :
  Lean.eq (Ne_ (Rt.get_horizon_of_task_T t)) (I.Prosa_Implementation_Refinements_Task_get_horizon_of_task_T IN IN1 (taskT_ex Ne_ t)).
Proof. exact (rf_trans _ _ _ (rf_horT_N_pfx _) (rf_congr (IABhor IN) _ _ (rf_geacT_N_ex t))). Qed.

Lemma rf_gtsT_N_ex t :
  Lean.eq (lex Ne_ (Rt.get_time_steps_of_task_T t))
    (I.Prosa_Implementation_Refinements_Task_get_time_steps_of_task_T IN IN1 (taskT_ex Ne_ t)).
Proof. exact (rf_trans _ _ _ (rf_time_steps_T_N_ex _) (rf_congr (IABts IN) _ _ (rf_geacT_N_ex t))). Qed.

Lemma rf_tswoT_N_ex t d :
  Lean.eq (lex Ne_ (Rt.time_steps_with_offset_T t d))
    (I.Prosa_Implementation_Refinements_Task_time_steps_with_offset_T IN IN1 INaddI (taskT_ex Ne_ t) (Ne_ d)).
Proof.
  unfold Rt.time_steps_with_offset_T.
  refine (rf_trans _ _ _ (rf_map_ex Ne_ Ne_ _ (fun x => INadd x (Ne_ d)) (fun x => rf_N_add_ex x d) _) _).
  exact (rf_congr (I.List_map_inst3 IN IN (fun x => INadd x (Ne_ d))) _ _ (rf_gtsT_N_ex t)).
Qed.

Lemma rf_rswoT_N_ex t os :
  Lean.eq (lex Ne_ (Rt.repeat_steps_with_offset_T t os))
    (I.Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T IN IN1 INaddI (taskT_ex Ne_ t) (lex Ne_ os)).
Proof.
  unfold Rt.repeat_steps_with_offset_T.
  refine (rf_trans _ _ _ (rf_flatten_ex Ne_ _) _).
  refine (rf_congr (I.List_flatten_inst1 IN) _ _ _).
  exact (rf_map_ex Ne_ (lex Ne_) _ _ (fun d => rf_tswoT_N_ex t d) _).
Qed.

Lemma rf_cmaT_N_ex t d :
  Lean.eq (Ne_ (Rt.ConcreteMaxArrivals_T t d))
    (I.Prosa_Implementation_Refinements_Task_ConcreteMaxArrivals_T IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI
       (taskT_ex Ne_ t) (Ne_ d)).
Proof.
  exact (rf_trans _ _ _ (rf_eac_T_N_ex _ d)
    (rf_congr (fun p => IABeac IN IN0 INaddI INmulI INdivI INmodI INleqI p (Ne_ d)) _ _ (rf_geacT_N_ex t))).
Qed.

Lemma rf_rbfT_N_ex t d :
  Lean.eq (Ne_ (Rt.task_rbf_T t d))
    (I.Prosa_Implementation_Refinements_Task_task_rbf_T IN IN0 IN1 INaddI INmulI INdivI INmodI INleqI
       (taskT_ex Ne_ t) (Ne_ d)).
Proof.
  exact (rf_trans _ _ _ (rf_N_mul_ex _ _) (rf_congr (INmul (Ne_ (Rt.task_cost_T t))) _ _ (rf_cmaT_N_ex t d))).
Qed.

Lemma rf_validT_N_pfx q :
  Lean.eq (be (Rab.valid_extrapolated_arrival_curve_T q)) (IABvalid IN IN0 IN1 INeqI INleqI INltI (pfx Ne_ q)).
Proof.
  destruct q as [h st]. unfold Rab.valid_extrapolated_arrival_curve_T.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _
    (rf_sorted_ex (pre Ne_ Ne_) _ _ rf_ltn_steps_T_N_ex st))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
  2: { refine (rf_trans _ _ _ (rf_has_ex Ne_ _ (fun s => INeqb s (Ne_ 1%N)) (fun s => rf_N_eqb_ex s 1%N) _) _).
       exact (rf_congr (fun l => I.List_any_inst1 IN l (fun s => INeqb s (Ne_ 1%N))) _ _ (rf_time_steps_T_N_ex (h, st))). }
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ _)).
  2: { refine (rf_trans _ _ _ (rf_N_eqb_ex _ N0) _).
       exact (rf_congr (fun v => INeqb v (Ne_ N0)) _ _ (rf_value_at_T_N_ex (h, st) N0)). }
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (rf_N_ltb_ex N0 h) _)).
  refine (rf_trans _ _ _ (rf_all_ex Ne_ _ (fun s => INleb s (Ne_ h)) (fun s => rf_N_leb_ex s h) _) _).
  exact (rf_congr (fun l => I.List_all_inst1 IN l (fun s => INleb s (Ne_ h))) _ _ (rf_time_steps_T_N_ex (h, st))).
Qed.

Lemma rf_vaT_N_ex t :
  Lean.eq (be (Rt.valid_arrivals_T t))
    (I.Prosa_Implementation_Refinements_Task_valid_arrivals_T IN IN0 IN1 INeqI INleqI INltI (taskT_ex Ne_ t)).
Proof.
  destruct t as [i c a d p]. unfold Rt.valid_arrivals_T. cbn.
  destruct a as [x|x|e]; cbn [tabT_ex].
  - exact (rf_N_leb_ex 1%N x).
  - exact (rf_N_leb_ex 1%N x).
  - exact (rf_validT_N_pfx e).
Qed.

(** Shape [refines (Rtask ==> R ==> R') f g]. *)
(** Shape [forall tsk : task_T, refines R (f (taskT_to_task tsk)) (g tsk)]. *)
Definition rf_corr_T {B B' BL B'L : Type} (eB : B -> BL) (eB' : B' -> B'L) (iB : BL -> B) (iB' : B'L -> B')
    (R : B -> B' -> Type) (RL : BL -> B'L -> Type)
    (fw : forall b b', R b b' -> RL (eB b) (eB' b')) (bw : forall c c', RL c c' -> R (iB c) (iB' c'))
    (rtB : forall b, iB (eB b) = b) (rtB' : forall b, iB' (eB' b) = b)
    (f : Dt.concrete_task -> B) (g : @Rt.task_T N -> B') (fL : ICT -> BL) (gL : ITT IN -> B'L)
    (Hf : forall t, Lean.eq (eB (f t)) (fL (task_ex t))) (Hg : forall t, Lean.eq (eB' (g t)) (gL (taskT_ex Ne_ t))) :
  TypeCorrespondence (forall tsk : @Rt.task_T N, refines R (f (Rt.taskT_to_task tsk)) (g tsk))
    (forall tsk : ITT IN, Iref _ _ RL (fL (I.Prosa_Implementation_Refinements_Task_taskT_to_task tsk)) (gL tsk)).
Proof.
  split.
  - intros s tL. apply Iref_mk.
    have o := fw _ _ (rf_ref_out (s (taskT_im Ni tL))).
    refine (rf_tr2 RL _ _ o).
    + refine (rf_trans _ _ _ (Hf _) (rf_congr fL _ _ _)).
      exact (rf_trans _ _ _ (rf_taskT2task_ex _)
        (rf_congr I.Prosa_Implementation_Refinements_Task_taskT_to_task _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
    + exact (rf_trans _ _ _ (Hg _) (rf_congr gL _ _ (rf_taskT_rtL Ne_ Ni rf_Ne_Ni tL))).
  - intros t tsk. apply rf_ref_in.
    have o := Iref_rel _ _ _ _ _ (t (taskT_ex Ne_ tsk)).
    have o' := bw _ _ (rf_tr2 RL
      (rf_sym _ _ (rf_trans _ _ _ (Hf _) (rf_congr fL _ _ (rf_taskT2task_ex tsk)))) (rf_sym _ _ (Hg tsk)) o).
    by rewrite rtB rtB' in o'.
Defined.

Lemma rf_sorted_leq_ex t :
  Lean.eq (be (sorted EAC.leq_steps (EAC.steps_of (Dt.get_arrival_curve_prefix t))))
    (IEsortedBool (IProd LN LN) I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps
       (IEsteps (IGACP (task_ex t)))).
Proof.
  refine (rf_trans _ _ _ (rf_sorted_ex (pre ne ne) _ _ rf_EAC_leq_steps_ex _) _).
  refine (rf_congr (IEsortedBool (IProd LN LN) I.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps) _ _ _).
  have h := rf_gacp_ex t. destruct (Dt.get_arrival_curve_prefix t) as [hh st].
  exact (rf_congr IEsteps _ _ h).
Qed.

Lemma rf_sorted_leqT_ex t :
  Lean.eq (be (sorted Rab.leq_steps_T (Rt.get_extrapolated_arrival_curve_T t).2))
    (IEsortedBool (IProd IN IN) (I.Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T IN INleqI)
       (I.Prod_snd_inst3 IN (IList (IProd IN IN)) (ITgeac IN IN1 (taskT_ex Ne_ t)))).
Proof.
  refine (rf_trans _ _ _ (rf_sorted_ex (pre Ne_ Ne_) _ _ rf_leq_steps_T_N_ex _) _).
  refine (rf_congr (IEsortedBool (IProd IN IN) (I.Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T IN INleqI)) _ _ _).
  have h := rf_geacT_N_ex t. destruct (Rt.get_extrapolated_arrival_curve_T t) as [hh st].
  exact (rf_congr (I.Prod_snd_inst3 IN (IList (IProd IN IN))) _ _ h).
Qed.