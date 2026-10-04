From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.
From prosa Require Import classic.model.time classic.util.div_mod util.seqset classic.model.priority classic.model.schedule.apa.affinity classic.model.schedule.apa.interference classic.analysis.apa.workload_bound classic.analysis.apa.interference_bound classic.analysis.apa.interference_bound_fp.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicInterferenceBoundFpApa.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicInterferenceBoundFpApaNatSub ClassicInterferenceBoundFpApaOps ClassicInterferenceBoundFpApaBase ClassicInterferenceBoundFpApaList ClassicInterferenceBoundFpApaList1 ClassicInterferenceBoundFpApaOrd.

Module I := ImportedClassicInterferenceBoundFpApa.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/apa/interference_bound_fp.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the task type is an [eqType], identified, with the Lean [DecidableEq]
    instance given by its decision procedure ([ct_decidable_eq]); times by
    [SubNatRel]; task parameters pointwise through [SubNatRel]; a sequence of
    (task, response time) pairs elementwise by the pair conversion [cibfp_pair]
    (task identified, time by [sub_nat_to_imported]); affinities by their underlying sequences through the ordinal conversion ([CafRel]), task affinities pointwise; FP policies pointwise;
    all with two-way totals.  [W]/[max_jobs]/[interference_bound_generic] as in the
    accepted classic workload_bound and interference_bound certificates (the classic
    [div_floor] through the accepted operation-level bridge [DivModCorrespondence],
    re-bound to this export); the sum over the pairs by induction on the sequence
    (the Lean side is the accepted v0.6 [sumFiltered] with pattern-matching
    functions, which compute on each pair). *)

Notation cid := (fun z => z).
Definition CsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Affinities (as in the accepted classic affinity certificate) *)

Section Aff.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation c := (co_ord_to_fin nR nL Hn).
Notation d := (co_fin_to_ord nR nL Hn).
Notation LAff := (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL).

Lemma caf_cd (y : Fin nL) : Logic.eq (c (d y)) y.
Proof. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn (d y)) (co_ord_surjective nR nL Hn y)). Qed.

Lemma caf_dc (x : 'I_nR) : Logic.eq (d (c x)) x.
Proof. exact (co_ord_eq _ _ _ _ _ (co_ord_surjective nR nL Hn (c x)) (co_ord_canonical nR nL Hn x)). Qed.

Lemma caf_c_rel (x : 'I_nR) (y : Fin nL) : CoOrdRel nR nL x y -> Logic.eq (c x) y.
Proof. intro H. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn x) H). Qed.

(** Affinities are related through their underlying sequences, elementwise by the ordinal conversion
    (Lean lists of [Fin n] at the universe instance [List_inst1], [ClassicAffinityList1]). *)
Notation LVal := (I.Prosa_Util_Seqset_set_val_inst1 (Fin nL) (I.instDecidableEqFin nL)).

Definition CafRel (aR : Affinity.affinity nR) (aL : LAff) : SProp :=
  ClListRel1 c (@prosa.util.seqset._set_seq _ aR) (LVal aL).

Definition caf_to_target (aR : Affinity.affinity nR) : LAff :=
  I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) (cl1_map c (@prosa.util.seqset._set_seq _ aR))
    (prop_to_sprop _ _ (cl1_uniq_rel _ _ c d caf_dc caf_cd _) (@prosa.util.seqset.set_uniq _ aR)).

Definition caf_to_source (aL : LAff) : Affinity.affinity nR :=
  @prosa.util.seqset.Build_set _ (cl1_unmap d (LVal aL))
    (interpret_strict _ (cl1_uniq_backward _ _ c d caf_cd _
                           (@I.nodup0 (Fin nL) (I.instDecidableEqFin nL) aL))).

Lemma caf_canonical aR : CafRel aR (caf_to_target aR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma caf_surjective aL : CafRel (caf_to_source aL) aL.
Proof. apply: coq_eq_to_imported_eq. exact (cl1_map_unmap c d caf_cd _). Qed.

Lemma caf_forall (PR : Affinity.affinity nR -> Prop) (PL : LAff -> SProp) :
  (forall aR aL, CafRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ CafRel caf_to_target caf_to_source caf_canonical caf_surjective PR PL). Qed.

Lemma caf_mem aR aL (Ha : CafRel aR aL) oR oL (Ho : CoOrdRel nR nL oR oL) :
  PropSPropRel (oR \in aR)
    (I.Membership_mem_inst3 (Fin nL) LAff (I.Prosa_Util_Seqset_instMembershipSet_inst1 (Fin nL) (I.instDecidableEqFin nL)) aL oL).
Proof.
  have E := caf_c_rel _ _ Ho. subst oL.
  exact (cl1_mem_rel_list _ _ c d caf_dc oR _ _ Ha).
Qed.
End Aff.

Section TaskAff.
Variables (Task : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation LTAff := (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task (ct_decidable_eq Task) nL).

Definition CtafRel (aR : Affinity.task_affinity Task nR) (aL : LTAff) : SProp :=
  forall tsk, CafRel nR nL Hn (aR tsk) (aL tsk).

Lemma cai_forall_taff (PR : Affinity.task_affinity Task nR -> Prop) (PL : LTAff -> SProp) :
  (forall aR aL, CtafRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof.
  exact (cs_forall_cover _ _ CtafRel (fun a tsk => caf_to_target nR nL Hn (a tsk)) (fun a tsk => caf_to_source nR nL Hn (a tsk))
           (fun a tsk => caf_canonical nR nL Hn (a tsk)) (fun a tsk => caf_surjective nR nL Hn (a tsk)) PR PL).
Qed.

Lemma cai_affinity_intersects aR aL (Ha : CafRel nR nL Hn aR aL) a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) :
  CtBoolRel (Affinity.affinity_intersects aR a'R)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity_intersects nL aL a'L).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ct_bool_and _ _ _ _ (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha oR oL Ho))
           (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha' oR oL Ho))).
Qed.
End TaskAff.


Section PolicyDefs.
Variables (Task : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).

Lemma cibfp_higher_priority_task_in aR aL (Ha : CtafRel Task nR nL Hn aR aL)
    hpR hpL (Hhp : forall a b, CtBoolRel (hpR a b) (hpL a b)) tsk a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) tsk_other :
  CtBoolRel (Interference.higher_priority_task_in aR hpR tsk a'R tsk_other)
    (I.Prosa_Classic_Model_Schedule_Apa_Interference_Interference_higher_priority_task_in Task dT nL aL hpL tsk a'L tsk_other).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_bool_and _ _ _ _ (Hhp tsk_other tsk) (ct_bool_not _ _ (ct_decide_eq Task tsk_other tsk)))
           (cai_affinity_intersects nR nL Hn _ _ Ha' _ _ (Ha tsk_other))).
Qed.

End PolicyDefs.

Lemma cib_max_jobs (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.max_jobs cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_max_jobs Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk)) (Hp tsk)).
Qed.

Lemma cib_W (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.W cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_W Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  have Hm := cib_max_jobs Task cR cL Hc pR pL Hp tsk RR RL HR dR dL Hd.
  exact (dm_add_correspondence _ _ _ _
           (ct_min_rel _ _ _ _ (Hc tsk)
              (dm_sub_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk))
                 (dm_mul_correspondence _ _ _ _ Hm (Hp tsk))))
           (dm_mul_correspondence _ _ _ _ Hm (Hc tsk))).
Qed.

Definition cibfp_pair (T : Type) (p : T * nat) : I.Prod_inst2 T Lean.Nat := I.Prod_mk_inst2 T Lean.Nat p.1 (sub_nat_to_imported p.2).

Lemma cib_generic (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk dR dL (Hd : SubNatRel dR dL)
    (p : Task * nat) :
  SubNatRel (InterferenceBoundGeneric.interference_bound_generic cR pR tsk dR p)
    (I.Prosa_Classic_Analysis_Apa_InterferenceBound_InterferenceBoundGeneric_interference_bound_generic Task (ct_decidable_eq Task) cL pL tsk dL (cibfp_pair Task p)).
Proof.
  exact (ct_min_rel _ _ _ _ (cib_W Task cR cL Hc pR pL Hp p.1 _ _ (sub_nat_rel_canonical p.2) _ _ Hd)
           (dm_add_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ Hd (Hc tsk)) (sub_nat_rel_canonical 1))).
Qed.

Definition cibfp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.


(** [\sum_(i <- l | P i) F i] against the accepted v0.6 [sumFiltered] ([((l.filter P).map F).sum]) along an element
    conversion, by induction (the filter through the re-bound [cl_filter]). *)
Lemma cibfp_sum_map (A B : Type) (c : A -> B) FR FL (HF : forall x, SubNatRel (FR x) (FL (c x))) : forall l,
  SubNatRel (\sum_(i <- l) FR i)
    (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
       (I.List_map_inst2 B Lean.Nat FL (cl_map c l))).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons. exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cibfp_sumFiltered_rel (A B : Type) (PR : A -> bool) FR (c : A -> B) PL FL
    (HP : forall x, CtBoolRel (PR x) (PL (c x))) (HF : forall x, SubNatRel (FR x) (FL (c x))) l L :
  ClListRel c l L -> SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered B L PL FL).
Proof.
  intro H.
  refine (cibfp_trs H (fun z => SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered B z PL FL)) _).
  rewrite -big_filter.
  refine (cibfp_trs (cl_lean_eq _ _ _ (cl_filter c PR PL HP l))
            (fun z => SubNatRel (\sum_(i <- filter PR l) FR i)
                        (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
                           (I.List_map_inst2 B Lean.Nat FL z))) _).
  exact (cibfp_sum_map A B c FR FL HF (filter PR l)).
Qed.

Theorem InterferenceBoundFP_total_interference_bound_fp_correspondence (Task : eqType) nR nL (Hn : SubNatRel nR nL)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL)
    aR aL (Ha : CtafRel Task nR nL Hn aR aL) tsk a'R a'L (Ha' : CafRel nR nL Hn a'R a'L)
    (Rp : seq (Task * nat)) RpL (HRp : ClListRel (cibfp_pair Task) Rp RpL) dR dL (Hd : SubNatRel dR dL)
    hpR hpL (Hhp : forall a b, CtBoolRel (hpR a b) (hpL a b)) :
  SubNatRel (InterferenceBoundFP.total_interference_bound_fp cR pR aR tsk a'R Rp dR hpR)
    (I.Prosa_Classic_Analysis_Apa_InterferenceBoundFp_InterferenceBoundFP_total_interference_bound_fp Task (ct_decidable_eq Task) cL pL nL aL tsk a'L RpL dL hpL).
Proof.
  rewrite /InterferenceBoundFP.total_interference_bound_fp.
  unfold I.Prosa_Classic_Analysis_Apa_InterferenceBoundFp_InterferenceBoundFP_total_interference_bound_fp.
  refine (cibfp_sumFiltered_rel (Task * nat) _ _ _ (cibfp_pair Task) _ _ _ _ _ _ HRp).
  - intros [a b]. exact (cibfp_higher_priority_task_in Task nR nL Hn aR aL Ha hpR hpL Hhp tsk a'R a'L Ha' a).
  - intros [a b]. exact (cib_generic Task cR cL Hc pR pL Hp tsk dR dL Hd (a, b)).
Qed.
