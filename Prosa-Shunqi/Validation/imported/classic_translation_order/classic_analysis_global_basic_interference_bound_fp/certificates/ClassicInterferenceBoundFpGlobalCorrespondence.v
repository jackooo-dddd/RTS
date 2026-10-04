From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.
From prosa Require Import classic.model.time classic.util.div_mod classic.analysis.global.basic.workload_bound classic.analysis.global.basic.interference_bound classic.analysis.global.basic.interference_bound_fp.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicInterferenceBoundFpGlobal.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicInterferenceBoundFpGlobalNatSub ClassicInterferenceBoundFpGlobalOps ClassicInterferenceBoundFpGlobalBase ClassicInterferenceBoundFpGlobalList.

Module I := ImportedClassicInterferenceBoundFpGlobal.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/global/basic/interference_bound_fp.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the task type is an [eqType], identified, with the Lean [DecidableEq]
    instance given by its decision procedure ([ct_decidable_eq]); times by
    [SubNatRel]; task parameters pointwise through [SubNatRel]; a sequence of
    (task, response time) pairs elementwise by the pair conversion [cibfp_pair]
    (task identified, time by [sub_nat_to_imported]);
    all with two-way totals.  [W]/[max_jobs]/[interference_bound_generic] as in the
    accepted classic workload_bound and interference_bound certificates (the classic
    [div_floor] through the accepted operation-level bridge [DivModCorrespondence],
    re-bound to this export); the sum over the pairs by induction on the sequence
    (the Lean side is the accepted v0.6 [sumSeq] with pattern-matching
    functions, which compute on each pair). *)

Notation cid := (fun z => z).
Definition CsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).


Lemma cib_max_jobs (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.max_jobs cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Basic_WorkloadBound_WorkloadBound_max_jobs Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk)) (Hp tsk)).
Qed.

Lemma cib_W (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.W cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Basic_WorkloadBound_WorkloadBound_W Task (ct_decidable_eq Task) cL pL tsk RL dL).
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
    (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBound_InterferenceBoundGeneric_interference_bound_generic Task (ct_decidable_eq Task) cL pL tsk dL (cibfp_pair Task p)).
Proof.
  exact (ct_min_rel _ _ _ _ (cib_W Task cR cL Hc pR pL Hp p.1 _ _ (sub_nat_rel_canonical p.2) _ _ Hd)
           (dm_add_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ Hd (Hc tsk)) (sub_nat_rel_canonical 1))).
Qed.

Definition cibfp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.


(** [\sum_(i <- l) F i] against [(l.map F).sum] along an element conversion, by induction; the accepted v0.6
    [sumSeq] ([(r.map F).sum]) and [sumFiltered] ([((r.filter P).map F).sum], the filter through the re-bound
    [cl_filter]) reduce to it. *)
Lemma cibfp_sum_map (A B : Type) (c : A -> B) FR FL (HF : forall x, SubNatRel (FR x) (FL (c x))) : forall l,
  SubNatRel (\sum_(i <- l) FR i)
    (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
       (I.List_map_inst2 B Lean.Nat FL (cl_map c l))).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons. exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.


Lemma cibfp_sumSeq_rel (A B : Type) FR (c : A -> B) FL (HF : forall x, SubNatRel (FR x) (FL (c x))) l L :
  ClListRel c l L -> SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq B L FL).
Proof.
  intro H. refine (cibfp_trs H (fun z => SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq B z FL)) _).
  exact (cibfp_sum_map A B c FR FL HF l).
Qed.

Theorem InterferenceBoundFP_total_interference_bound_fp_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    (Rp : seq (Task * nat)) RpL (HRp : ClListRel (cibfp_pair Task) Rp RpL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (InterferenceBoundFP.total_interference_bound_fp cR pR tsk Rp dR)
    (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundFp_InterferenceBoundFP_total_interference_bound_fp Task (ct_decidable_eq Task) cL pL tsk RpL dL).
Proof.
  rewrite /InterferenceBoundFP.total_interference_bound_fp.
  unfold I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundFp_InterferenceBoundFP_total_interference_bound_fp.
  refine (cibfp_sumSeq_rel (Task * nat) _ _ (cibfp_pair Task) _ _ _ _ HRp).
  intros [a b]. exact (cib_generic Task cR cL Hc pR pL Hp tsk dR dL Hd (a, b)).
Qed.
