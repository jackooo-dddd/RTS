From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.
From prosa Require Import classic.model.time classic.model.suspension.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicSuspension.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicSuspensionBase ClassicSuspensionList.

Module I := ImportedClassicSuspension.
Local Open Scope nat_scope.

(** Certificates for [classic/model/suspension.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times and durations by [SubNatRel]; job
    and task parameters [X -> time] pointwise through [SubNatRel]; suspension functions [Job -> time -> duration]
    pointwise on related times ([CsuSuspRel]); all with two-way totals.

    Computation: the half-open sum [\sum_(0 <= t < job_cost j) next_suspension j t] against the projected Lean fold
    [List.foldr Nat.add 0 (List.map _ (List.range' 0 (job_cost j - 0) 1))] — the export form of [total_suspension]
    (a definition-body projection guarded by the kernel-checked [rfl] equality
    [ClassicSuspensionInterface.total_suspension_proj_guard], as for the accepted classic schedule certificate's
    [service]) — related by [csu_ico] as in the accepted classic sum / schedule certificates. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

Definition ct_coq_false_to_target (H : Logic.False) : I.False := match H return I.False with end.

Definition ct_target_false_to_strict (H : I.False) : StrictlyInhabited Logic.False := match H with end.

Definition ct_decidable_eq (T : eqType) : I.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => I.Decidable_isTrue (Lean.eq x y) (coq_eq_to_imported_eq x y H)
    | ReflectF H => I.Decidable_isFalse (Lean.eq x y)
        (fun HL => ct_coq_false_to_target (H (imported_eq_to_coq_eq x y HL)))
    end.

Lemma ct_eq_rel (T : Type) (x y : T) : PropSPropRel (Logic.eq x y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. exact (strictly_inhabits (imported_eq_to_coq_eq x y H)).
Qed.

Lemma ct_forall_identity (A : Type) (PR : A -> Prop) (PL : A -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) -> PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (H x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x. exact (sprop_to_prop _ _ (H x) (HL x)).
Qed.

Lemma ct_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall n, PR n) (forall n, PL n).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _ (H _ _ (sub_nat_rel_surjective nL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro nR. exact (sprop_to_prop _ _ (H _ _ (sub_nat_rel_canonical nR)) (HL _)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma csu_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma csu_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma csu_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma csu_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma csu_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CsuParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma csu_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsuParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (csu_forall_cover _ _ (CsuParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint csu_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csu_snatl s') end.

Lemma csu_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (csu_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (csu_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma csu_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csu_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csu_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma csu_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsuFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma csu_fun_canonical FR FL (HF : CsuFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma csu_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma csu_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsuFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := csu_nat_sub_canonical nR mR.
  rewrite csu_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (csu_foldr_add FL FR (csu_fun_canonical FR FL HF)).
  by rewrite csu_big_fold.
Qed.


(* ------------------------------------------------------------------ *)
(** * Suspension functions *)

Section Susp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CsuSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition csu_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition csu_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma csu_susp_canonical sR : CsuSuspRel sR (csu_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold csu_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma csu_susp_surjective sL : CsuSuspRel (csu_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma csu_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CsuSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (csu_forall_cover _ _ CsuSuspRel csu_susp_to_target csu_susp_to_source csu_susp_canonical csu_susp_surjective PR PL). Qed.
End Susp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem Suspension_job_suspension_correspondence (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CsuSuspRel Job sR (csu_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CsuSuspRel Job (csu_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (csu_susp_canonical Job) (csu_susp_surjective Job)). Qed.

Theorem Suspension_total_suspension_correspondence (Job : eqType) cR cL (Hc : CsuParRel Job cR cL) sR sL (Hs : CsuSuspRel Job sR sL) j :
  SubNatRel (Suspension.total_suspension cR sR j) (I.Prosa_Classic_Model_Suspension_Suspension_total_suspension Job (ct_decidable_eq Job) cL sL j).
Proof. exact (csu_ico 0 _ (cR j) (cL j) (sR j) (sL j) (sub_nat_rel_canonical 0) (Hc j) (Hs j)). Qed.

Theorem Suspension_dynamic_suspension_model_correspondence (Task Job : eqType) cR cL (Hc : CsuParRel Job cR cL)
    (job_task : Job -> Task) sR sL (Hs : CsuSuspRel Job sR sL) bR bL (Hb : CsuParRel Task bR bL) :
  PropSPropRel (Suspension.dynamic_suspension_model cR job_task sR bR)
    (I.Prosa_Classic_Model_Suspension_Suspension_dynamic_suspension_model Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) cL job_task sL bL).
Proof.
  apply: ct_forall_identity => j.
  exact (sub_nat_le_correspondence _ _ _ _ (Suspension_total_suspension_correspondence Job cR cL Hc sR sL Hs j) (Hb (job_task j))).
Qed.
