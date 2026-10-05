From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import PreemptionParameterSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPreemptionParameter ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedPreemptionParameter.
Module S := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module L := prosa.util.list.ListSemanticSource.
Module G := prosa.GeneratedNondecreasingSource.GeneratedNondecreasingSource.

(** Definition certificates for [model/preemption/parameter.v].

    Source side: the extracted byte-identical class and definition blocks
    [S.X] (over the accepted utility sources [L.range]/[L.max0]/[L.last0] and
    [G.distances]) and the extracted remark statement; target side: the
    compiled Lean declarations.  Inputs: [JobPreemptable] pointwise (Nat
    progress by [SubNatRel], Booleans; two-way totals below), [job_cost] by the
    accepted [SvcJobCostRel], processor states and schedules by the accepted
    two-sided [SvcProcessorStateRel]/[SvcScheduleRel], arrival sequences by
    [ArArrivalSequenceRel], the JLDP policy pointwise on Booleans.  Nat-list
    operations are related through kernel-checked Lean constructor equations
    exported with the artifact (the accepted Nondecreasing interface for
    [distances], the rank-local interface for filter, membership, [range],
    [max0] and [last0]). *)

Notation P_natFilter := I.Prosa_Validation_PreemptionParameterInterface_natFilter.
Notation P_natMem := I.Prosa_Validation_PreemptionParameterInterface_natMem.
Notation P_natFoldMax := I.Prosa_Validation_PreemptionParameterInterface_natFoldMax.

Lemma pp_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma pp_succ_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> SubNatRel nR.+1 (svc_target_add nL svc_target_one).
Proof.
  intro Hn. have H := svc_target_add_related nR nL 1 svc_target_one Hn (sub_nat_rel_canonical 1).
  rewrite addn1 in H. exact H.
Qed.

Lemma pp_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (I.Iff_intro PL QL
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (I.Iff_mp PL QL H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (I.Iff_mpr PL QL H (prop_to_sprop _ _ HQ q)).
Qed.

(** ** Nat-list operations *)

Definition PpNatPredRel (PR : nat -> bool) (PL : Lean.Nat -> I.Bool) : SProp :=
  forall nR nL, SubNatRel nR nL -> ArBoolRel (PR nR) (PL nL).

Lemma pp_filter_canonical PR PL (HP : PpNatPredRel PR PL) (xs : seq nat) :
  SvcNatListRel (filter PR xs) (P_natFilter PL (svc_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_PreemptionParameterInterface_production_natFilter_nil PL)).
  - have Hx := HP x (sub_nat_to_imported x) (sub_nat_rel_canonical x).
    unfold SvcNatListRel in IH |- *. cbn [filter].
    case_eq (PR x) => Hb; rewrite Hb in Hx; cbn [svc_nat_list_to_imported].
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_PreemptionParameterInterface_production_natFilter_cons_true PL
          (sub_nat_to_imported x) (svc_nat_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_imported_eq_congr (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x)) _ _ IH).
    + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_PreemptionParameterInterface_production_natFilter_cons_false PL
          (sub_nat_to_imported x) (svc_nat_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma pp_filter_related PR PL (HP : PpNatPredRel PR PL) xsR xsL :
  SvcNatListRel xsR xsL -> SvcNatListRel (filter PR xsR) (P_natFilter PL xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _ (pp_filter_canonical PR PL HP xsR)
    (sub_imported_eq_congr (P_natFilter PL) _ _ Hxs)).
Qed.

Lemma pp_range_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcNatListRel (L.range aR bR) (I.Prosa_Util_List_range aL bL).
Proof.
  intros Ha Hb. unfold L.range, index_iota.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
    (I.Prosa_Validation_PreemptionParameterInterface_production_range_eq aL bL))).
  exact (svc_range_related _ _ _ _ Ha (svc_target_sub_related _ _ _ _ (pp_succ_related _ _ Hb) Ha)).
Qed.

Lemma pp_nat_eq_transport (xR yR : nat) (xL yL : Lean.Nat) :
  xR = yR -> SubNatRel xR xL -> SubNatRel yR yL -> Lean.eq xL yL.
Proof.
  intros H Hx Hy. destruct H.
  exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
Qed.

Lemma pp_nat_eqb_related (xR yR : nat) (xL yL : Lean.Nat) :
  SubNatRel xR xL -> SubNatRel yR yL ->
  ArBoolRel (xR == yR) (I.Decidable_decide (Lean.eq xL yL) (I.instDecidableEqNat xL yL)).
Proof.
  intros Hx Hy. unfold ArBoolRel.
  destruct (xR == yR) eqn:E.
  - have H : xR = yR by apply/eqP.
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_PreemptionParameterInterface_production_nat_decide_eq_true xL yL
        (pp_nat_eq_transport _ _ _ _ H Hx Hy))).
  - have NE : xR <> yR by (move=> H; rewrite H eqxx in E).
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_PreemptionParameterInterface_production_nat_decide_eq_false xL yL
        (fun EL => ar_coq_false_to_target
          (NE (Logic.eq_trans (Logic.eq_sym (pp_nat_input _ _ Hx))
            (Logic.eq_trans (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ EL))
              (pp_nat_input _ _ Hy))))))).
Qed.

Lemma pp_bool_or_canonical (aR bR : bool) :
  Lean.eq (ar_bool_to_imported (aR || bR))
    (I.Bool_or (ar_bool_to_imported aR) (ar_bool_to_imported bR)).
Proof. destruct aR, bR; exact (@Lean.eq_refl _ _). Qed.

Lemma pp_bool_or_related aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL -> ArBoolRel (aR || bR) (I.Bool_or aL bL).
Proof.
  intros Ha Hb. unfold ArBoolRel in *.
  exact (sub_imported_eq_trans _ _ _ (pp_bool_or_canonical aR bR)
    (sub_imported_eq_congr2 I.Bool_or _ _ _ _ Ha Hb)).
Qed.

Lemma pp_mem_canonical (x : nat) (xs : seq nat) :
  ArBoolRel (x \in xs) (P_natMem (sub_nat_to_imported x) (svc_nat_list_to_imported xs)).
Proof.
  induction xs as [|y ys IH].
  - exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_PreemptionParameterInterface_production_natMem_nil
        (sub_nat_to_imported x))).
  - rewrite in_cons. cbn [svc_nat_list_to_imported].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_PreemptionParameterInterface_production_natMem_cons
        (sub_nat_to_imported x) (sub_nat_to_imported y) (svc_nat_list_to_imported ys)))).
    exact (pp_bool_or_related _ _ _ _
      (pp_nat_eqb_related x y (sub_nat_to_imported x) (sub_nat_to_imported y)
        (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) IH).
Qed.

Lemma pp_mem_related xR xL xsR xsL :
  SubNatRel xR xL -> SvcNatListRel xsR xsL ->
  PropSPropRel (is_true (xR \in xsR))
    (Lean.eq (I.Decidable_decide
      (I.Membership_mem_inst3 Lean.Nat (I.List_inst1 Lean.Nat)
        (I.List_instMembership_inst1 Lean.Nat) xsL xL)
      (I.List_instDecidableMemOfLawfulBEq_inst1 Lean.Nat
        (I.instBEqOfDecidableEq_inst1 Lean.Nat I.instDecidableEqNat)
        I.Nat_instLawfulBEq xL xsL)) I.Bool_true).
Proof.
  intros Hx Hxs. apply ar_bool_truth_correspondence. unfold ArBoolRel.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
    (I.Prosa_Validation_PreemptionParameterInterface_production_mem_eq xL xsL))).
  exact (sub_imported_eq_trans _ _ _ (pp_mem_canonical xR xsR)
    (sub_imported_eq_congr2 P_natMem _ _ _ _ Hx Hxs)).
Qed.

Lemma pp_distances_canonical (xs : seq nat) :
  SvcNatListRel (G.distances xs) (I.Prosa_Util_Nondecreasing_distances (svc_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _ I.Prosa_Validation_NondecreasingInterface_production_distances_nil).
  - destruct xs as [|y ys].
    + exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_NondecreasingInterface_production_distances_single (sub_nat_to_imported x))).
    + have Hs : Logic.eq (G.distances [:: x, y & ys]) ((y - x) :: G.distances (y :: ys)).
      { cbn [G.distances drop zip map]. rewrite drop0. reflexivity. }
      unfold SvcNatListRel in IH |- *. rewrite Hs. cbn [svc_nat_list_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_NondecreasingInterface_production_distances_cons
          (sub_nat_to_imported x) (sub_nat_to_imported y) (svc_nat_list_to_imported ys)))).
      exact (sub_imported_eq_congr2 (I.List_cons_inst1 Lean.Nat) _ _ _ _
        (svc_target_sub_related _ _ _ _ (sub_nat_rel_canonical y) (sub_nat_rel_canonical x)) IH).
Qed.

Lemma pp_distances_related xsR xsL :
  SvcNatListRel xsR xsL -> SvcNatListRel (G.distances xsR) (I.Prosa_Util_Nondecreasing_distances xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _ (pp_distances_canonical xsR)
    (sub_imported_eq_congr I.Prosa_Util_Nondecreasing_distances _ _ Hxs)).
Qed.

Lemma pp_max_canonical (a b : nat) :
  Lean.eq (I.Nat_max (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (maxn a b)).
Proof.
  have Hle := sub_nat_le_correspondence a (sub_nat_to_imported a) b (sub_nat_to_imported b)
    (sub_nat_rel_canonical a) (sub_nat_rel_canonical b).
  have Hge := sub_nat_le_correspondence b (sub_nat_to_imported b) a (sub_nat_to_imported a)
    (sub_nat_rel_canonical b) (sub_nat_rel_canonical a).
  destruct (leq a b) eqn:Hab.
  - have Hm : maxn a b = b := elimT maxn_idPr Hab.
    rewrite Hm.
    exact (I.Prosa_Validation_PreemptionParameterInterface_production_max_of_le _ _
      (prop_to_sprop _ _ Hle isT)).
  - have Hba : is_true (leq b a).
    { apply: ltnW. rewrite ltnNge Hab. done. }
    have Hm : maxn a b = a := elimT maxn_idPl Hba.
    rewrite Hm.
    exact (I.Prosa_Validation_PreemptionParameterInterface_production_max_of_ge _ _
      (prop_to_sprop _ _ Hge Hba)).
Qed.

Lemma pp_foldmax_canonical (z : nat) (xs : seq nat) :
  Lean.eq (P_natFoldMax (sub_nat_to_imported z) (svc_nat_list_to_imported xs))
    (sub_nat_to_imported (foldl maxn z xs)).
Proof.
  revert z. induction xs as [|x xs IH]; intro z.
  - exact (I.Prosa_Validation_PreemptionParameterInterface_production_natFoldMax_nil _).
  - cbn [svc_nat_list_to_imported foldl].
    refine (sub_imported_eq_trans _ _ _
      (I.Prosa_Validation_PreemptionParameterInterface_production_natFoldMax_cons _ _ _) _).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr (fun m => P_natFoldMax m (svc_nat_list_to_imported xs)) _ _
        (pp_max_canonical z x)) _).
    exact (IH (maxn z x)).
Qed.

Lemma pp_max0_related xsR xsL :
  SvcNatListRel xsR xsL -> SubNatRel (L.max0 xsR) (I.Prosa_Util_List_max0 xsL).
Proof.
  intro Hxs. unfold SubNatRel, L.max0.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
    (I.Prosa_Validation_PreemptionParameterInterface_production_max0_eq xsL))).
  refine (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (pp_foldmax_canonical 0 xsR)) _).
  exact (sub_imported_eq_congr (P_natFoldMax (sub_nat_to_imported 0)) _ _ Hxs).
Qed.

Lemma pp_last0_canonical (xs : seq nat) :
  SubNatRel (L.last0 xs) (I.Prosa_Util_List_last0 (svc_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _ I.Prosa_Validation_PreemptionParameterInterface_production_last0_nil).
  - destruct xs as [|y ys].
    + exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_PreemptionParameterInterface_production_last0_single (sub_nat_to_imported x))).
    + have Hs : Logic.eq (L.last0 [:: x, y & ys]) (L.last0 (y :: ys)) by reflexivity.
      unfold SubNatRel in IH |- *. rewrite Hs. cbn [svc_nat_list_to_imported].
      exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_PreemptionParameterInterface_production_last0_cons2
          (sub_nat_to_imported x) (sub_nat_to_imported y) (svc_nat_list_to_imported ys)))).
Qed.

Lemma pp_last0_related xsR xsL :
  SvcNatListRel xsR xsL -> SubNatRel (L.last0 xsR) (I.Prosa_Util_List_last0 xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _ (pp_last0_canonical xsR)
    (sub_imported_eq_congr I.Prosa_Util_List_last0 _ _ Hxs)).
Qed.

(** ** The [JobPreemptable] class (input relation with two-way totals) *)

Section Class.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Definition PpJobPreemptableRel (jpR : S.JobPreemptable Job)
      (jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ) : SProp :=
    forall j : Job, PpNatPredRel (@S.job_preemptable Job jpR j)
      (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j).

  Lemma JobPreemptable_source_total (jpR : S.JobPreemptable Job) :
    PpJobPreemptableRel jpR
      (I.Prosa_Model_Preemption_Parameter_JobPreemptable_mk Job dJ
        (fun j nL => ar_bool_to_imported (jpR j (sub_nat_to_rocq nL)))).
  Proof.
    intros j nR nL Hn. unfold ArBoolRel. cbn.
    rewrite (pp_nat_input _ _ Hn). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma JobPreemptable_target_total
      (jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ) :
    PpJobPreemptableRel
      ((fun j n => ar_bool_to_rocq
        (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
          (sub_nat_to_imported n))) : S.JobPreemptable Job) jpL.
  Proof.
    intros j nR nL Hn. unfold ArBoolRel.
    refine (sub_imported_eq_trans _ _ _ (ar_bool_target_roundtrip _) _).
    exact (sub_imported_eq_congr
      (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j) _ _ Hn).
  Qed.
End Class.

(** ** Definitions of the max/last nonpreemptive segments *)

Section Segments.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : S.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.

  Theorem job_preemption_points_correspondence (j : Job) :
    SvcNatListRel (@S.job_preemption_points Job costR jpR j)
      (I.Prosa_Model_Preemption_Parameter_job_preemption_points Job dJ costL jpL j).
  Proof.
    unfold S.job_preemption_points.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_PreemptionParameterInterface_production_job_preemption_points_eq
        Job dJ costL jpL j))).
    exact (pp_filter_related _ _ (Hjp j) _ _
      (pp_range_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))).
  Qed.

  Theorem lengths_of_segments_correspondence (j : Job) :
    SvcNatListRel (@S.lengths_of_segments Job costR jpR j)
      (I.Prosa_Model_Preemption_Parameter_lengths_of_segments Job dJ costL jpL j).
  Proof.
    unfold S.lengths_of_segments.
    cbn [I.Prosa_Model_Preemption_Parameter_lengths_of_segments].
    exact (pp_distances_related _ _ (job_preemption_points_correspondence j)).
  Qed.

  Theorem job_max_nonpreemptive_segment_correspondence (j : Job) :
    SubNatRel (@S.job_max_nonpreemptive_segment Job costR jpR j)
      (I.Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job dJ costL jpL j).
  Proof.
    unfold S.job_max_nonpreemptive_segment.
    cbn [I.Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment].
    exact (pp_max0_related _ _ (lengths_of_segments_correspondence j)).
  Qed.

  Theorem job_last_nonpreemptive_segment_correspondence (j : Job) :
    SubNatRel (@S.job_last_nonpreemptive_segment Job costR jpR j)
      (I.Prosa_Model_Preemption_Parameter_job_last_nonpreemptive_segment Job dJ costL jpL j).
  Proof.
    unfold S.job_last_nonpreemptive_segment.
    cbn [I.Prosa_Model_Preemption_Parameter_job_last_nonpreemptive_segment].
    exact (pp_last0_related _ _ (lengths_of_segments_correspondence j)).
  Qed.

  Theorem job_rtct_correspondence (j : Job) :
    SubNatRel (@S.job_rtct Job costR jpR j)
      (I.Prosa_Model_Preemption_Parameter_job_rtct Job dJ costL jpL j).
  Proof.
    unfold S.job_rtct.
    cbn [I.Prosa_Model_Preemption_Parameter_job_rtct].
    exact (svc_target_sub_related _ _ _ _ (Hcost j)
      (svc_target_sub_related _ _ _ _ (job_last_nonpreemptive_segment_correspondence j)
        (sub_nat_rel_canonical 1))).
  Qed.

  Theorem job_cannot_be_nonpreemptive_after_completion_correspondence (j : Job) :
    ArBoolRel (@S.job_cannot_be_nonpreemptive_after_completion Job costR jpR j)
      (I.Prosa_Model_Preemption_Parameter_job_cannot_be_nonpreemptive_after_completion
        Job dJ costL jpL j).
  Proof.
    unfold S.job_cannot_be_nonpreemptive_after_completion.
    cbn [I.Prosa_Model_Preemption_Parameter_job_cannot_be_nonpreemptive_after_completion].
    exact (Hjp j _ _ (Hcost j)).
  Qed.

  Theorem conversion_preserves_equivalence_correspondence :
    PropSPropRel (ltac:(let s := constr:(fun H : S.statement_conversion_preserves_equivalence =>
      H Job costR jpR) in let T := type of s in match T with _ -> ?B => exact B end))
      (ltac:(let T := type of (@I.Prosa_Model_Preemption_Parameter_conversion_preserves_equivalence
        Job dJ costL jpL) in exact T)).
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros rR rL Hr.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hr (Hcost j))|].
    apply pp_iff_correspondence.
    - exact (ar_bool_truth_correspondence _ _ (Hjp j _ _ Hr)).
    - exact (pp_mem_related _ _ _ _ Hr (job_preemption_points_correspondence j)).
  Qed.
End Segments.

Lemma job_cannot_become_nonpreemptive_before_execution_correspondence (Job : eqType)
    jpR jpL (Hjp : PpJobPreemptableRel Job jpR jpL) (j : Job) :
  ArBoolRel (@S.job_cannot_become_nonpreemptive_before_execution Job jpR j)
    (I.Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution
      Job (ar_decidable_eq Job) jpL j).
Proof.
  unfold S.job_cannot_become_nonpreemptive_before_execution.
  cbn [I.Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution].
  exact (Hjp j _ _ (sub_nat_rel_canonical O)).
Qed.

(** ** Schedule-dependent definitions *)

Section Model.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : S.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Lemma pp_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.scheduled_at.
    cbn [I.Prosa_Behavior_Service_scheduled_at].
    exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma pp_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma pp_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      (sub_nat_rel_canonical O) Ht (fun xR xL Hx => pp_service_at_related j xR xL Hx).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j O tR)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j Lean.Nat_zero tL)) in Hsum.
    exact Hsum.
  Qed.

  Lemma pp_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j) (pp_service_related j tR tL Ht)).
  Qed.

  Theorem preempted_at_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@S.preempted_at Job costR PStateR schedR j tR)
      (I.Prosa_Model_Preemption_Parameter_preempted_at Job dJ costL PStateL schedL j tL).
  Proof.
    intro Ht. unfold S.preempted_at.
    cbn [I.Prosa_Model_Preemption_Parameter_preempted_at].
    rewrite -subn1.
    apply ar_bool_and_related; [apply ar_bool_and_related|].
    - exact (pp_scheduled_at_related j _ _
        (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical 1))).
    - exact (svc_bool_not_related _ _ (pp_completed_by_related j tR tL Ht)).
    - exact (svc_bool_not_related _ _ (pp_scheduled_at_related j tR tL Ht)).
  Qed.

  Theorem not_preemptive_implies_scheduled_correspondence (j : Job) :
    PropSPropRel (@S.not_preemptive_implies_scheduled Job jpR PStateR schedR j)
      (I.Prosa_Model_Preemption_Parameter_not_preemptive_implies_scheduled
        Job dJ jpL PStateL schedL j).
  Proof.
    unfold S.not_preemptive_implies_scheduled.
    cbn [I.Prosa_Model_Preemption_Parameter_not_preemptive_implies_scheduled].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (svc_bool_not_related _ _ (Hjp j _ _ (pp_service_related j tR tL Ht)))).
    - exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related j tR tL Ht)).
  Qed.

  Theorem execution_starts_with_preemption_point_correspondence (j : Job) :
    PropSPropRel (@S.execution_starts_with_preemption_point Job jpR PStateR schedR j)
      (I.Prosa_Model_Preemption_Parameter_execution_starts_with_preemption_point
        Job dJ jpL PStateL schedL j).
  Proof.
    unfold S.execution_starts_with_preemption_point.
    cbn [I.Prosa_Model_Preemption_Parameter_execution_starts_with_preemption_point].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    have Ht1 := pp_succ_related tR tL Ht.
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (svc_bool_not_related _ _ (pp_scheduled_at_related j tR tL Ht))).
    - apply ar_imp_correspondence.
      + exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related j _ _ Ht1)).
      + exact (ar_bool_truth_correspondence _ _ (Hjp j _ _ (pp_service_related j _ _ Ht1))).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem valid_preemption_model_correspondence :
    PropSPropRel (@S.valid_preemption_model Job costR jpR PStateR arrR schedR)
      (I.Prosa_Model_Preemption_Parameter_valid_preemption_model
        Job dJ costL jpL PStateL arrL schedL).
  Proof.
    unfold S.valid_preemption_model.
    cbn [I.Prosa_Model_Preemption_Parameter_valid_preemption_model].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_and_correspondence.
    { exact (ar_bool_truth_correspondence _ _
        (job_cannot_become_nonpreemptive_before_execution_correspondence Job jpR jpL Hjp j)). }
    apply ar_and_correspondence.
    { exact (ar_bool_truth_correspondence _ _
        (job_cannot_be_nonpreemptive_after_completion_correspondence Job costR costL Hcost
          jpR jpL Hjp j)). }
    apply ar_and_correspondence.
    - exact (not_preemptive_implies_scheduled_correspondence j).
    - exact (execution_starts_with_preemption_point_correspondence j).
  Qed.

  Variable pR : prosa.model.priority.definitions.JLDP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ.
  Hypothesis Hp : forall tR tL, SubNatRel tR tL -> forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job_at Job pR tR x y)
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ pL tL x y).

  Theorem no_superfluous_preemptions_correspondence :
    PropSPropRel (@S.no_superfluous_preemptions Job costR pR PStateR schedR)
      (I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions
        Job dJ costL pL PStateL schedL).
  Proof.
    unfold S.no_superfluous_preemptions.
    cbn [I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro jhp.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (preempted_at_correspondence j tR tL Ht))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related jhp tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp tR tL Ht j jhp))).
  Qed.
End Model.
