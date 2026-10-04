From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.sum classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.arrival.curves.bounds classic.model.schedule.uni.workload classic.analysis.uni.arrival_curves.workload_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniArrivalCurvesWorkloadBound.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniArrivalCurvesWorkloadBoundBase ClassicUniArrivalCurvesWorkloadBoundList.

Module I := ImportedClassicUniArrivalCurvesWorkloadBound.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/arrival_curves/workload_bound.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job/task parameters
    pointwise through [SubNatRel]; arrival curves [Task -> time -> nat] pointwise on related arguments; task sequences
    elementwise; FP policies pointwise on Booleans; arrival sequences pointwise on related times; all with two-way
    totals.  The imported job, priority, task-arrival, arrival-curve and workload definitions are related as in the
    accepted classic certificates (re-bound below, through the kernel-checked [sumSeq] / [sumFiltered] / [bigCat]
    equations of [ClassicUniArrivalCurvesWorkloadBoundInterface]).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used).  The binder lists put [task_cost] before the job type; the job type is fixed as an [eqType] with its
    canonical Lean instance and [task_cost] stays universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cwb_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cwb_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cwb_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cwb_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cwb_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cwb_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cwb_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cwb_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cwb_unmap_rel T l) PR PL).
Qed.

Definition CwbParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cwb_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CwbParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cwb_forall_cover _ _ (CwbParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cwb_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cwb_natl s') end.

Definition cwb_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cwb_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cwb_one) (cwb_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cwb_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cwb_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cwb_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cwb_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cwb_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cwb_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cwb_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cwb_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cwb_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cwb_cl_append. reflexivity.
Qed.

Lemma cwb_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CwbFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cwb_bigcat_rel (A : Type) fR fL (Hf : CwbFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicUniArrivalCurvesWorkloadBoundInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cwb_iota_range (nR - mR) 0) cwb_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cwb_cl_map_ext _ _ Hpt) (cwb_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cwb_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cwb_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CwbArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cwb_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cwb_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cwb_arr_canonical aR : CwbArrRel aR (cwb_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cwb_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cwb_arr_surjective aL : CwbArrRel (cwb_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cwb_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CwbArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cwb_forall_cover _ _ CwbArrRel cwb_arr_to_target cwb_arr_to_source cwb_arr_canonical cwb_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cwb_jobs_arrived_between aR aL (Ha : CwbArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cwb_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cwb_arrives_in aR aL (Ha : CwbArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cwb_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cwb_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniArrivalCurvesWorkloadBoundInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicUniArrivalCurvesWorkloadBoundInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cwb_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cwb_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cwb_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniArrivalCurvesWorkloadBoundInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniArrivalCurvesWorkloadBoundInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniArrivalCurvesWorkloadBoundInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cwb_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cwb_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CwbPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cwb_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CwbPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cwb_forall_cover _ _ (CwbPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CwbRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cwb_rel_canonical (T : Type) (rR : T -> T -> bool) : CwbRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cwb_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CwbRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cwb_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CwbRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cwb_forall_cover _ _ (CwbRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cwb_rel_canonical T) (cwb_rel_surjective T) PR PL).
Qed.

Definition CwbJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CwbRelRel T (rR tR) (rL tL).

Lemma cwb_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CwbJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cwb_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CwbJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cwb_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CwbJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cwb_forall_cover _ _ (CwbJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cwb_jldp_canonical T) (cwb_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cwb_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CwbRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CwbRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cwb_rel_canonical Task) (cwb_rel_surjective Task)). Qed.

Lemma cwb_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CwbRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CwbRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cwb_rel_canonical Job) (cwb_rel_surjective Job)). Qed.

Lemma cwb_PR_FP_to_JLFP (job_task : Job -> Task) rR rL (Hr : CwbRelRel Task rR rL) :
  CwbRelRel Job (Priority.FP_to_JLFP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLFP Task Job dT dJ job_task rL).
Proof. intros a b. exact (Hr (job_task a) (job_task b)). Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cwb_J_job_cost_le_task_cost tcR tcL (Htc : CwbParRel Task tcR tcL) cR cL (Hc : CwbParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cwb_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma cwb_TA_arrivals_of_task_between (job_task : Job -> Task) aR aL (Ha : CwbArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (cwb_TA_is_job_of_task job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cwb_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.

Lemma cwb_TA_num_arrivals_of_task (job_task : Job -> Task) aR aL (Ha : CwbArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrival.num_arrivals_of_task job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_num_arrivals_of_task Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  have H := cwb_TA_arrivals_of_task_between job_task aR aL Ha tsk _ _ _ _ H1 H2.
  change (SubNatRel (size (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R))
    (I.List_length Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L))).
  exact (match H in Lean.eq _ z
               return SubNatRel (size (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)) (I.List_length Job z) with
         | Lean.eq_refl => cl_size cid _
         end).
Qed.

End TaskArrivalDefs.

Section AcboundsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

(** Curves [Task -> nat -> nat] pointwise on related arguments. *)
Definition CwbCurveRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk nR nL, SubNatRel nR nL -> SubNatRel (fR tsk nR) (fL tsk nL).

Notation NA := (cwb_TA_num_arrivals_of_task Task Job).

Lemma cwb_AC_is_arrival_bound (job_task : Job -> Task) aR aL (Ha : CwbArrRel Job aR aL)
    mR mL (Hm : CwbCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.is_arrival_bound job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_is_arrival_bound Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  exact (sub_nat_le_correspondence _ _ _ _ (NA job_task aR aL Ha tsk _ _ _ _ H1 H2) (Hm tsk _ _ (ct_sub_rel _ _ _ _ H2 H1))).
Qed.

Lemma cwb_AC_is_arrival_bound_for_taskset (job_task : Job -> Task) aR aL (Ha : CwbArrRel Job aR aL)
    mR mL (Hm : CwbCurveRel mR mL) tsR tsL (Hts : ClListRel cid tsR tsL) :
  PropSPropRel (ArrivalCurves.is_arrival_bound_for_taskset job_task aR mR tsR)
    (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_is_arrival_bound_for_taskset Task dT Job dJ job_task aL mL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_mem Task tsk _ _ Hts).
  exact (cwb_AC_is_arrival_bound job_task aR aL Ha mR mL Hm tsk).
Qed.

End AcboundsDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cwb_WL_workload_of_jobs cR cL (Hc : CwbParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CwbPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (cwb_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

End UwlDefs.



(* ------------------------------------------------------------------ *)
(** * Arrival curves [Task -> time -> nat], with two-way totals *)

Lemma cwb_curve_canonical (Task : eqType) mR : CwbCurveRel Task mR (fun tsk nL => sub_nat_to_imported (mR tsk (sub_nat_to_rocq nL))).
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cwb_curve_surjective (Task : eqType) mL : CwbCurveRel Task (fun tsk nR => sub_nat_to_rocq (mL tsk (sub_nat_to_imported nR))) mL.
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. exact (sub_nat_rel_surjective _). Qed.

Lemma cwb_forall_curve (Task : eqType) (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall mR mL, CwbCurveRel Task mR mL -> PropSPropRel (PR mR) (PL mL)) -> PropSPropRel (forall m, PR m) (forall m, PL m).
Proof. exact (cwb_forall_cover _ _ (CwbCurveRel Task) _ _ (cwb_curve_canonical Task) (cwb_curve_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CwbParRel Task tcR tcL.
Variables (mR : Task -> nat -> nat) (mL : Task -> Lean.Nat -> Lean.Nat).
Hypothesis Hm : CwbCurveRel Task mR mL.

Theorem MaxArrivalsWorkloadBound_task_request_bound_function_correspondence tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.task_request_bound_function tcR mR tsk dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_task_request_bound_function Task dT tcL mL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Hm tsk _ _ Hd)). Qed.

Notation TRBF := MaxArrivalsWorkloadBound_task_request_bound_function_correspondence.

Theorem MaxArrivalsWorkloadBound_total_request_bound_function_correspondence tsR tsL (Hts : ClListRel cid tsR tsL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_request_bound_function tcR mR tsR dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_request_bound_function Task dT tcL mL tsL dL).
Proof. exact (cwb_sum_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _ Hts). Qed.

Theorem MaxArrivalsWorkloadBound_total_hep_request_bound_function_FP_correspondence hR hL (Hh : CwbRelRel Task hR hL)
    tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_hep_request_bound_function_FP tcR hR mR tsR tsk dR)
    (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_hep_request_bound_function_FP Task dT tcL hL mL tsL tsk dL).
Proof. exact (cwb_sum_filtered_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _ (fun x => Hh x tsk) _ _ Hts). Qed.

Theorem MaxArrivalsWorkloadBound_total_ohep_request_bound_function_FP_correspondence hR hL (Hh : CwbRelRel Task hR hL)
    tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_ohep_request_bound_function_FP tcR hR mR tsR tsk dR)
    (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_ohep_request_bound_function_FP Task dT tcL hL mL tsL tsk dL).
Proof.
  exact (cwb_sum_filtered_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _
           (fun x => ct_bool_and _ _ _ _ (Hh x tsk) (ct_bool_not _ _ (ct_decide_eq Task x tsk))) _ _ Hts).
Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation WL := cwb_WL_workload_of_jobs.

Definition src_task_workload_le_task_rbf (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time, ltac:(type_of_term (@MaxArrivalsWorkloadBound.task_workload_le_task_rbf Task task_cost Job)).
Definition tgt_task_workload_le_task_rbf (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_task_workload_le_task_rbf Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).

Theorem MaxArrivalsWorkloadBound_task_workload_le_task_rbf_correspondence (Task Job : eqType) :
  PropSPropRel (src_task_workload_le_task_rbf Task Job) (tgt_task_workload_le_task_rbf Task Job).
Proof.
  unfold src_task_workload_le_task_rbf, tgt_task_workload_le_task_rbf.
  apply: cwb_forall_par => tcR tcL Htc. apply: cwb_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => arrR arrL Harr.
  apply: cwb_forall_list => tsR tsL Hts. apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_mem Task tsk _ _ Hts).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cwb_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cwb_J_job_cost_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task j)). }
  apply: cwb_forall_curve => mR mL Hm.
  apply: ct_imp; first exact (cwb_AC_is_arrival_bound_for_taskset Task Job job_task arrR arrL Harr mR mL Hm _ _ Hts).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd.
  have A := cwb_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hd).
  exact (sub_nat_le_correspondence _ _ _ _ (WL Job cR cL Hc _ _ A _ _ (fun x => ct_decide_eq Task (job_task x) (job_task j)))
           (MaxArrivalsWorkloadBound_task_request_bound_function_correspondence Task tcR tcL Htc mR mL Hm tsk _ _ Hd)).
Qed.
Definition src_total_workload_le_total_rbf (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time, ltac:(type_of_term (@MaxArrivalsWorkloadBound.total_workload_le_total_rbf Task task_cost Job)).
Definition tgt_total_workload_le_total_rbf (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_workload_le_total_rbf Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).

Theorem MaxArrivalsWorkloadBound_total_workload_le_total_rbf_correspondence (Task Job : eqType) :
  PropSPropRel (src_total_workload_le_total_rbf Task Job) (tgt_total_workload_le_total_rbf Task Job).
Proof.
  unfold src_total_workload_le_total_rbf, tgt_total_workload_le_total_rbf.
  apply: cwb_forall_par => tcR tcL Htc. apply: cwb_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => arrR arrL Harr.
  apply: cwb_forall_rel => hR hL Hh. apply: cwb_forall_list => tsR tsL Hts. apply: ct_forall_identity => tsk.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cwb_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cwb_J_job_cost_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task j)). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cwb_arrives_in Job arrR arrL Harr j).
    exact (cwb_mem Task (job_task j) _ _ Hts). }
  apply: cwb_forall_curve => mR mL Hm.
  apply: ct_imp; first exact (cwb_AC_is_arrival_bound_for_taskset Task Job job_task arrR arrL Harr mR mL Hm _ _ Hts).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd.
  have A := cwb_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hd).
  exact (sub_nat_le_correspondence _ _ _ _
           (WL Job cR cL Hc _ _ A _ _ (fun x => ct_bool_and _ _ _ _ (cwb_PR_FP_to_JLFP Task Job job_task hR hL Hh x j)
                                                     (ct_bool_not _ _ (ct_decide_eq Task (job_task x) (job_task j)))))
           (MaxArrivalsWorkloadBound_total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc mR mL Hm hR hL Hh _ _ Hts tsk _ _ Hd)).
Qed.
Definition src_total_workload_le_total_rbf' (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time, ltac:(type_of_term (@MaxArrivalsWorkloadBound.total_workload_le_total_rbf' Task task_cost Job)).
Definition tgt_total_workload_le_total_rbf' (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_workload_le_total_rbf' Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).

Theorem MaxArrivalsWorkloadBound_total_workload_le_total_rbf'_correspondence (Task Job : eqType) :
  PropSPropRel (src_total_workload_le_total_rbf' Task Job) (tgt_total_workload_le_total_rbf' Task Job).
Proof.
  unfold src_total_workload_le_total_rbf', tgt_total_workload_le_total_rbf'.
  apply: cwb_forall_par => tcR tcL Htc. apply: cwb_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => arrR arrL Harr.
  apply: cwb_forall_rel => hR hL Hh. apply: cwb_forall_list => tsR tsL Hts. apply: ct_forall_identity => tsk.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cwb_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cwb_J_job_cost_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task j)). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cwb_arrives_in Job arrR arrL Harr j).
    exact (cwb_mem Task (job_task j) _ _ Hts). }
  apply: cwb_forall_curve => mR mL Hm.
  apply: ct_imp; first exact (cwb_AC_is_arrival_bound_for_taskset Task Job job_task arrR arrL Harr mR mL Hm _ _ Hts).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd.
  have A := cwb_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hd).
  exact (sub_nat_le_correspondence _ _ _ _
           (WL Job cR cL Hc _ _ A _ _ (fun x => cwb_PR_FP_to_JLFP Task Job job_task hR hL Hh x j))
           (MaxArrivalsWorkloadBound_total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc mR mL Hm hR hL Hh _ _ Hts tsk _ _ Hd)).
Qed.
Definition src_total_workload_le_total_rbf'' (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time, ltac:(type_of_term (@MaxArrivalsWorkloadBound.total_workload_le_total_rbf'' Task task_cost Job)).
Definition tgt_total_workload_le_total_rbf'' (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_workload_le_total_rbf'' Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).

Theorem MaxArrivalsWorkloadBound_total_workload_le_total_rbf''_correspondence (Task Job : eqType) :
  PropSPropRel (src_total_workload_le_total_rbf'' Task Job) (tgt_total_workload_le_total_rbf'' Task Job).
Proof.
  unfold src_total_workload_le_total_rbf'', tgt_total_workload_le_total_rbf''.
  apply: cwb_forall_par => tcR tcL Htc. apply: cwb_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => arrR arrL Harr.
  apply: cwb_forall_list => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cwb_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cwb_J_job_cost_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task j)). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cwb_arrives_in Job arrR arrL Harr j).
    exact (cwb_mem Task (job_task j) _ _ Hts). }
  apply: cwb_forall_curve => mR mL Hm.
  apply: ct_imp; first exact (cwb_AC_is_arrival_bound_for_taskset Task Job job_task arrR arrL Harr mR mL Hm _ _ Hts).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd.
  have A := cwb_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hd).
  exact (sub_nat_le_correspondence _ _ _ _
           (WL Job cR cL Hc _ _ A _ _ (fun x => ct_bool_canonical true))
           (MaxArrivalsWorkloadBound_total_request_bound_function_correspondence Task tcR tcL Htc mR mL Hm _ _ Hts _ _ Hd)).
Qed.
