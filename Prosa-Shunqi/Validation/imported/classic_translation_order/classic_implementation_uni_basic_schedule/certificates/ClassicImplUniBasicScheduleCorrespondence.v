From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.minmax classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.basic.platform classic.model.schedule.uni.transformation.construction classic.implementation.uni.basic.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplUniBasicSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplUniBasicScheduleBase ClassicImplUniBasicScheduleList.

Module I := ImportedClassicImplUniBasicSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/uni/basic/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); times by [SubNatRel]; job parameters pointwise through [SubNatRel]; arrival sequences
    pointwise on related times; JLDP policies pointwise on related times (Booleans); uniprocessor schedules pointwise
    through the option map; all with two-way totals.  [seq_min] as in the accepted classic minmax certificate; the
    construction from prefixes as in the accepted classic uniprocessor construction certificate (re-bound below; the
    construction function [highest_priority_job] maps related schedules and instants to related choices, so the
    scheduler itself is related to its Lean counterpart); [schedule_prefix] through its kernel-checked Lean recursion
    equations exported with the artifact.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used); every input is quantified and covered in both directions. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cub_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cub_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cub_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cub_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cub_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cub_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cub_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cub_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cub_unmap_rel T l) PR PL).
Qed.

Definition CubParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cub_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CubParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cub_forall_cover _ _ (CubParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cub_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cub_natl s') end.

Definition cub_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cub_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cub_one) (cub_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cub_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cub_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cub_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cub_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cub_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cub_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cub_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cub_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cub_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cub_cl_append. reflexivity.
Qed.

Lemma cub_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CubFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cub_bigcat_rel (A : Type) fR fL (Hf : CubFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplUniBasicScheduleInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cub_iota_range (nR - mR) 0) cub_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cub_cl_map_ext _ _ Hpt) (cub_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cub_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cub_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CubArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cub_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cub_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cub_arr_canonical aR : CubArrRel aR (cub_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cub_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cub_arr_surjective aL : CubArrRel (cub_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cub_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CubArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cub_forall_cover _ _ CubArrRel cub_arr_to_target cub_arr_to_source cub_arr_canonical cub_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cub_jobs_arrived_between aR aL (Ha : CubArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cub_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cub_arrives_in aR aL (Ha : CubArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cub_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cub_consistent pR pL (Hp : CubParRel Job pR pL) aR aL (Ha : CubArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cub_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cub_jobs_arrived_up_to aR aL (Ha : CubArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_up_to aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_up_to Job dJ aL tL).
Proof. exact (cub_jobs_arrived_between Job aR aL Ha 0 _ tR.+1 _ (sub_nat_rel_canonical 0) (cub_succ_rel tR tL Ht)). Qed.

Lemma cub_arrives_at aR aL (Ha : CubArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cub_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cub_has_arrived pR pL (Hp : CubParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cub_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cub_snatl s') end.

Lemma cub_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cub_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cub_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cub_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cub_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cub_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cub_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CubFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cub_fun_canonical FR FL (HF : CubFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cub_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cub_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CubFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cub_nat_sub_canonical nR mR.
  rewrite cub_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cub_foldr_add FL FR (cub_fun_canonical FR FL HF)).
  by rewrite cub_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cub_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cub_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cub_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cub_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cub_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CubSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cub_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cub_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cub_sched_canonical sR : CubSchedRel sR (cub_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cub_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cub_sched_surjective sL : CubSchedRel (cub_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cub_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cub_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CubSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cub_forall_cover _ _ CubSchedRel cub_sched_to_target cub_sched_to_source cub_sched_canonical cub_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cub_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CubSchedRel Job sR (cub_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CubSchedRel Job (cub_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cub_sched_canonical Job) (cub_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CubSchedRel Job sR sL.

Lemma cub_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cub_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cub_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cub_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cub_US_scheduled_at j tR tL Ht)). Qed.

Lemma cub_service_at_fun j : CubFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cub_US_service_at j kR kL Hk). Qed.

Lemma cub_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cub_ico _ _ _ _ _ _ H1 H2 (cub_service_at_fun j)). Qed.

Lemma cub_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cub_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cub_US_completed_by cR cL (Hc : CubParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cub_US_service j tR tL Ht)). Qed.

Lemma cub_US_pending aR aL (Ha : CubParRel Job aR aL) cR cL (Hc : CubParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cub_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cub_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cub_US_backlogged aR aL (Ha : CubParRel Job aR aL) cR cL (Hc : CubParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cub_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cub_US_scheduled_at j tR tL Ht))).
Qed.

Lemma cub_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CubArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cub_US_scheduled_at j tR tL Ht)).
  exact (cub_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cub_US_jobs_must_arrive_to_execute aR aL (Ha : CubParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cub_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cub_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cub_US_completed_jobs_dont_execute cR cL (Hc : CubParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cub_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CubRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cub_rel_canonical (T : Type) (rR : T -> T -> bool) : CubRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cub_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CubRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cub_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CubRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cub_forall_cover _ _ (CubRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cub_rel_canonical T) (cub_rel_surjective T) PR PL).
Qed.

Definition CubJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CubRelRel T (rR tR) (rL tL).

Lemma cub_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CubJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cub_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CubJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cub_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CubJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cub_forall_cover _ _ (CubJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cub_jldp_canonical T) (cub_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cub_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CubJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CubJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (cub_jldp_canonical Job) (cub_jldp_surjective Job)). Qed.

End PriodefsDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CubSchedRel Job sR sL.

Lemma cub_UP_work_conserving aR aL (Ha : CubParRel Job aR aL) cR cL (Hc : CubParRel Job cR cL)
    arrR arrL (Harr : CubArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cub_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cub_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cub_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

Lemma cub_UP_respects_JLDP_policy aR aL (Ha : CubParRel Job aR aL) cR cL (Hc : CubParRel Job cR cL)
    arrR arrL (Harr : CubArrRel Job arrR arrL) hR hL (Hh : CubJldpRel Job hR hL) :
  PropSPropRel (Platform.respects_JLDP_policy aR cR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_respects_JLDP_policy Job dJ aL cL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cub_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cub_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cub_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End UplatDefs.

(* ------------------------------------------------------------------ *)
(** * [seq_min] (as in the accepted classic minmax certificate) *)

Lemma cub_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite !cl_unopt_opt in E'.
Qed.

Section MinmaxArg.
Variables (T1 : eqType) (T2R : eqType) (T2L : Type) (d2 : I.DecidableEq T2L).
Variables (relR : T2R -> T2R -> bool) (relL : T2L -> T2L -> I.Bool) (FR : T1 -> T2R) (FL : T1 -> T2L).
Hypothesis Hcomp : forall x y, CtBoolRel (relR (FR x) (FR y)) (relL (FL x) (FL y)).
Notation d1 := (ct_decidable_eq T1).

Lemma cub_argmin_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL x) (FL y)) I.Bool_true) (I.instDecidableEqBool (relL (FL x) (FL y)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma cub_argmin_rel : forall l,
  Logic.eq (cl_opt (seq_argmin relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite cub_argmin_step -IH.
  case: (seq_argmin relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp x y)). by case: (relR (FR x) (FR y)).
Qed.

Lemma cub_argmin_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmin relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -cub_argmin_rel. exact (cub_opt_eq _ _). Qed.

End MinmaxArg.

Lemma cub_seq_min (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_min relR l)) (I.Prosa_Classic_Util_Minmax_seq_min T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (cub_argmin_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma cub_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cub_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cub_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cub_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma cub_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

(* ------------------------------------------------------------------ *)
(** * Construction from prefixes, specialised at related inputs

    As in the accepted v0.6 [implementation/facts/generic_schedule.v] certificate: the construction function
    [build_schedule : schedule Job -> time -> option Job] is a higher-order input; the certificates below are stated for
    any source function and any Lean function that agree (through the option map) on related schedules and related
    instants ([Hbuild]), and for related base schedules ([Hbase]); the predicate [P] of the last statement is related
    pointwise through the option map ([HP]).  Inside the statements every quantified schedule, instant and job is covered
    in both directions. *)

Section UconsConstruction.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Variable buildR : UniprocessorSchedule.schedule Job -> nat -> option Job.
Variable buildL : LSched -> Lean.Nat -> I.Option Job.
Hypothesis Hbuild : forall sR sL, CubSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CubSchedRel Job baseR baseL.

Lemma cub_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Lemma cub_UC_update_schedule prevR prevL (Hprev : CubSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CubSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (cub_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma cub_prefix_canonical (mR : nat) :
  CubSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (cub_trs (cub_lsym (I.Prosa_Validation_ClassicImplUniBasicScheduleInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CubSchedRel Job _ z) _).
    exact (cub_UC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cub_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (cub_trs Hm1 (fun z => CubSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (cub_trs (cub_lsym (I.Prosa_Validation_ClassicImplUniBasicScheduleInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CubSchedRel Job _ z) _).
    exact (cub_UC_update_schedule _ _ IH _ _ Hm1).
Qed.

Lemma cub_UC_schedule_prefix mR mL (Hm : SubNatRel mR mL) :
  CubSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (cub_trs Hm (fun z => CubSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (cub_prefix_canonical mR)). Qed.

Lemma cub_UC_build_schedule_from_prefixes :
  CubSchedRel Job (@ScheduleConstruction.build_schedule_from_prefixes Job buildR baseR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ buildL baseL).
Proof. intros tR tL Ht. exact (cub_UC_schedule_prefix tR tL Ht tR tL Ht). Qed.

End UconsConstruction.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CubParRel Job jaR jaL) (Hc : CubParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CubArrRel Job aR aL.
Variables (hR : nat -> Job -> Job -> bool) (hL : Lean.Nat -> Job -> Job -> I.Bool).
Hypothesis Hh : CubJldpRel Job hR hL.

Theorem ConcreteScheduler_pending_jobs_correspondence sR sL (Hs : CubSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@ConcreteScheduler.pending_jobs Job jaR cR aR sR tR) (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_pending_jobs Job dJ jaL cL aL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cub_jobs_arrived_up_to Job aR aL Ha tR tL Ht).
  have F := cl_filter cid _ (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ jaL cL sL j tL)
              (fun j => cub_US_pending Job sR sL Hs jaR jaL Hja cR cL Hc j tR tL Ht) (ArrivalSequence.jobs_arrived_up_to aR tR).
  rewrite -E in F. exact F.
Qed.

Theorem ConcreteScheduler_highest_priority_job_correspondence sR sL (Hs : CubSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@ConcreteScheduler.highest_priority_job Job jaR cR aR hR sR tR)) (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_highest_priority_job Job dJ jaL cL aL hL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite /ConcreteScheduler.highest_priority_job (cub_seq_min Job (hR tR) (hL tL) (Hh tR tL Ht)).
  rewrite -(cl_list_logic _ _ _ (ConcreteScheduler_pending_jobs_correspondence sR sL Hs tR tL Ht)).
  reflexivity.
Qed.

Lemma cub_empty : CubSchedRel Job (fun _ => None) (fun _ => I.Option_none Job).
Proof. intros tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteScheduler_scheduler_correspondence :
  CubSchedRel Job (@ConcreteScheduler.scheduler Job jaR cR aR hR) (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler Job dJ jaL cL aL hL).
Proof.
  exact (cub_UC_build_schedule_from_prefixes Job _ _ ConcreteScheduler_highest_priority_job_correspondence _ _ cub_empty).
Qed.
End Defs.

Notation SCH := ConcreteScheduler_scheduler_correspondence.
Notation HPJ := ConcreteScheduler_highest_priority_job_correspondence.

(** [transitive r], unfolded on the Lean side (as in the accepted classic minmax certificate). *)
Lemma cub_trans (T : Type) (R : T -> T -> bool) RL (HR : forall a b, CtBoolRel (R a b) (RL a b)) :
  PropSPropRel (transitive R)
    (forall y x z, Lean.eq (RL x y) I.Bool_true -> Lean.eq (RL y z) I.Bool_true -> Lean.eq (RL x z) I.Bool_true).
Proof.
  rewrite /transitive. apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR x y)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR y z)) (ct_bool_truth _ _ (HR x z))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_scheduler_depends_only_on_prefix (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_depends_only_on_prefix Job)).
Definition tgt_scheduler_depends_only_on_prefix (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler_depends_only_on_prefix Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_depends_only_on_prefix_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_depends_only_on_prefix Job) (tgt_scheduler_depends_only_on_prefix Job).
Proof.
  unfold src_scheduler_depends_only_on_prefix, tgt_scheduler_depends_only_on_prefix.
  apply: cub_forall_par => jaR jaL Hja. apply: cub_forall_par => cR cL Hc.
  apply: (cub_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cub_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cub_forall_jldp Job) => hR hL Hh.
  apply: (cub_forall_sched Job) => s1R s1L Hs1. apply: (cub_forall_sched Job) => s2R s2L Hs2.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp.
  { apply: ct_forall_nat => t0R t0L Ht0.
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht0 Ht).
    exact (cub_opt_rel_eq _ _ _ _ _ (Hs1 t0R t0L Ht0) (Hs2 t0R t0L Ht0)). }
  exact (cub_opt_rel_eq _ _ _ _ _ (HPJ Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh s1R s1L Hs1 tR tL Ht)
           (HPJ Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh s2R s2L Hs2 tR tL Ht)).
Qed.

Definition src_scheduler_uses_construction_function (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_uses_construction_function Job)).
Definition tgt_scheduler_uses_construction_function (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler_uses_construction_function Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_uses_construction_function_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_uses_construction_function Job) (tgt_scheduler_uses_construction_function Job).
Proof.
  unfold src_scheduler_uses_construction_function, tgt_scheduler_uses_construction_function.
  apply: cub_forall_par => jaR jaL Hja. apply: cub_forall_par => cR cL Hc.
  apply: (cub_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cub_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cub_forall_jldp Job) => hR hL Hh.
  apply: ct_forall_nat => tR tL Ht.
  have Hs := SCH Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh.
  exact (cub_opt_rel_eq _ _ _ _ _ (Hs tR tL Ht) (HPJ Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh _ _ Hs tR tL Ht)).
Qed.

Definition src_scheduler_jobs_come_from_arrival_sequence (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_come_from_arrival_sequence Job)).
Definition tgt_scheduler_jobs_come_from_arrival_sequence (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_jobs_come_from_arrival_sequence Job) (tgt_scheduler_jobs_come_from_arrival_sequence Job).
Proof.
  unfold src_scheduler_jobs_come_from_arrival_sequence, tgt_scheduler_jobs_come_from_arrival_sequence.
  apply: cub_forall_par => jaR jaL Hja. apply: cub_forall_par => cR cL Hc.
  apply: (cub_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cub_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cub_forall_jldp Job) => hR hL Hh.
  exact (cub_US_jobs_come_from_arrival_sequence Job _ _ (SCH Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh) aR aL Ha).
Qed.

Definition src_scheduler_jobs_must_arrive_to_execute (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_must_arrive_to_execute Job)).
Definition tgt_scheduler_jobs_must_arrive_to_execute (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler_jobs_must_arrive_to_execute Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_jobs_must_arrive_to_execute_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_jobs_must_arrive_to_execute Job) (tgt_scheduler_jobs_must_arrive_to_execute Job).
Proof.
  unfold src_scheduler_jobs_must_arrive_to_execute, tgt_scheduler_jobs_must_arrive_to_execute.
  apply: cub_forall_par => jaR jaL Hja. apply: cub_forall_par => cR cL Hc.
  apply: (cub_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cub_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cub_forall_jldp Job) => hR hL Hh.
  exact (cub_US_jobs_must_arrive_to_execute Job _ _ (SCH Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh) jaR jaL Hja).
Qed.

Definition src_scheduler_completed_jobs_dont_execute (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_completed_jobs_dont_execute Job)).
Definition tgt_scheduler_completed_jobs_dont_execute (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler_completed_jobs_dont_execute Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_completed_jobs_dont_execute_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_completed_jobs_dont_execute Job) (tgt_scheduler_completed_jobs_dont_execute Job).
Proof.
  unfold src_scheduler_completed_jobs_dont_execute, tgt_scheduler_completed_jobs_dont_execute.
  apply: cub_forall_par => jaR jaL Hja. apply: cub_forall_par => cR cL Hc.
  apply: (cub_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cub_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cub_forall_jldp Job) => hR hL Hh.
  exact (cub_US_completed_jobs_dont_execute Job _ _ (SCH Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh) cR cL Hc).
Qed.

Definition src_scheduler_work_conserving (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_work_conserving Job)).
Definition tgt_scheduler_work_conserving (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler_work_conserving Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_work_conserving_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_work_conserving Job) (tgt_scheduler_work_conserving Job).
Proof.
  unfold src_scheduler_work_conserving, tgt_scheduler_work_conserving.
  apply: cub_forall_par => jaR jaL Hja. apply: cub_forall_par => cR cL Hc.
  apply: (cub_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cub_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cub_forall_jldp Job) => hR hL Hh.
  exact (cub_UP_work_conserving Job _ _ (SCH Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh) jaR jaL Hja cR cL Hc aR aL Ha).
Qed.

Definition src_scheduler_respects_policy (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_respects_policy Job)).
Definition tgt_scheduler_respects_policy (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Basic_Schedule_ConcreteScheduler_scheduler_respects_policy Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_respects_policy_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_respects_policy Job) (tgt_scheduler_respects_policy Job).
Proof.
  unfold src_scheduler_respects_policy, tgt_scheduler_respects_policy.
  apply: cub_forall_par => jaR jaL Hja. apply: cub_forall_par => cR cL Hc.
  apply: (cub_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cub_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cub_forall_jldp Job) => hR hL Hh.
  apply: ct_imp; first exact (ct_forall_nat _ _ (fun tR tL Ht => cub_trans Job (hR tR) (hL tL) (Hh tR tL Ht))).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht. apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    exact (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hh tR tL Ht x y) (Hh tR tL Ht y x))). }
  exact (cub_UP_respects_JLDP_policy Job _ _ (SCH Job jaR jaL cR cL Hja Hc aR aL Ha hR hL Hh) jaR jaL Hja cR cL Hc aR aL Ha hR hL Hh).
Qed.
