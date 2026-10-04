From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.list classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.basic.platform classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.busy_interval classic.model.schedule.uni.limited.platform.priority_inversion_is_bounded.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicPriorityInversionBounded.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicPriorityInversionBoundedBase ClassicPriorityInversionBoundedList.



Module I := ImportedClassicPriorityInversionBounded.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/platform/priority_inversion_is_bounded.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the eqTypes'
    decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters pointwise
    through [SubNatRel]; arrival sequences pointwise on related times; JLFP policies pointwise on Booleans; uniprocessor
    schedules pointwise through the option map; all with two-way totals.  The service, workload, arrival, job, schedule
    and platform notions as in the accepted classic certificates (re-bound below); the limited busy-interval and limited-preemption platform notions as in the accepted classic certificates (re-bound
    below); [\max_(x <- s | P x) F x] against the v0.6 [maxFiltered] through its exported equation [maxFiltered_eq_foldr_cond];
    [cumulative_priority_inversion] through a kernel-guarded [rfl] body projection; [a ==> b] against [!a || b]; the informative reflection
    [quiet_time_P] by constructor-preserving maps in both directions (as in the accepted classic record certificates).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used); every input is quantified and covered in both directions. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cqi_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cqi_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cqi_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cqi_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cqi_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cqi_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cqi_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cqi_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cqi_unmap_rel T l) PR PL).
Qed.

Definition CqiParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cqi_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CqiParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cqi_forall_cover _ _ (CqiParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cqi_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cqi_natl s') end.

Definition cqi_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cqi_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cqi_one) (cqi_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cqi_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cqi_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cqi_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cqi_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cqi_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cqi_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cqi_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cqi_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cqi_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cqi_cl_append. reflexivity.
Qed.

Lemma cqi_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CqiFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cqi_bigcat_rel (A : Type) fR fL (Hf : CqiFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPriorityInversionBoundedInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cqi_iota_range (nR - mR) 0) cqi_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cqi_cl_map_ext _ _ Hpt) (cqi_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cqi_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cqi_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CqiArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cqi_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cqi_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cqi_arr_canonical aR : CqiArrRel aR (cqi_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cqi_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cqi_arr_surjective aL : CqiArrRel (cqi_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cqi_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CqiArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cqi_forall_cover _ _ CqiArrRel cqi_arr_to_target cqi_arr_to_source cqi_arr_canonical cqi_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cqi_jobs_arrived_between aR aL (Ha : CqiArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cqi_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cqi_arrives_in aR aL (Ha : CqiArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cqi_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cqi_consistent pR pL (Hp : CqiParRel Job pR pL) aR aL (Ha : CqiArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cqi_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cqi_jobs_arrived_before aR aL (Ha : CqiArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cqi_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cqi_arrives_at aR aL (Ha : CqiArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cqi_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cqi_has_arrived pR pL (Hp : CqiParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma cqi_arrived_before pR pL (Hp : CqiParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

Lemma cqi_arrived_between pR pL (Hp : CqiParRel Job pR pL) j t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  CtBoolRel (ArrivalSequence.arrived_between pR j t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_between Job dJ pL j t1L t2L).
Proof. exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hp j)) (ct_decide_lt _ _ _ _ (Hp j) H2)). Qed.

End ArrivalDefs2.

Fixpoint cqi_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cqi_snatl s') end.

Lemma cqi_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cqi_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cqi_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cqi_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cqi_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cqi_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cqi_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CqiFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cqi_fun_canonical FR FL (HF : CqiFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cqi_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cqi_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CqiFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cqi_nat_sub_canonical nR mR.
  rewrite cqi_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cqi_foldr_add FL FR (cqi_fun_canonical FR FL HF)).
  by rewrite cqi_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cqi_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cqi_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cqi_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cqi_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cqi_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CqiSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cqi_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cqi_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cqi_sched_canonical sR : CqiSchedRel sR (cqi_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cqi_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cqi_sched_surjective sL : CqiSchedRel (cqi_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cqi_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cqi_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CqiSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cqi_forall_cover _ _ CqiSchedRel cqi_sched_to_target cqi_sched_to_source cqi_sched_canonical cqi_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cqi_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CqiSchedRel Job sR (cqi_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CqiSchedRel Job (cqi_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cqi_sched_canonical Job) (cqi_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqiSchedRel Job sR sL.

Lemma cqi_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cqi_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cqi_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cqi_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cqi_US_scheduled_at j tR tL Ht)). Qed.

Lemma cqi_service_at_fun j : CqiFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cqi_US_service_at j kR kL Hk). Qed.

Lemma cqi_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cqi_ico _ _ _ _ _ _ H1 H2 (cqi_service_at_fun j)). Qed.

Lemma cqi_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cqi_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cqi_US_completed_by cR cL (Hc : CqiParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cqi_US_service j tR tL Ht)). Qed.

Lemma cqi_US_pending aR aL (Ha : CqiParRel Job aR aL) cR cL (Hc : CqiParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cqi_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cqi_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cqi_US_backlogged aR aL (Ha : CqiParRel Job aR aL) cR cL (Hc : CqiParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cqi_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cqi_US_scheduled_at j tR tL Ht))).
Qed.

Lemma cqi_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CqiArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_scheduled_at j tR tL Ht)).
  exact (cqi_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cqi_US_jobs_must_arrive_to_execute aR aL (Ha : CqiParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cqi_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cqi_US_completed_jobs_dont_execute cR cL (Hc : CqiParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cqi_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cqi_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicPriorityInversionBoundedInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicPriorityInversionBoundedInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cqi_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cqi_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cqi_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicPriorityInversionBoundedInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicPriorityInversionBoundedInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicPriorityInversionBoundedInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cqi_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cqi_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CqiPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cqi_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CqiPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cqi_forall_cover _ _ (CqiPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CqiRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cqi_rel_canonical (T : Type) (rR : T -> T -> bool) : CqiRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cqi_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CqiRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cqi_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CqiRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cqi_forall_cover _ _ (CqiRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cqi_rel_canonical T) (cqi_rel_surjective T) PR PL).
Qed.

Definition CqiJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CqiRelRel T (rR tR) (rL tL).

Lemma cqi_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CqiJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cqi_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CqiJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cqi_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CqiJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cqi_forall_cover _ _ (CqiJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cqi_jldp_canonical T) (cqi_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cqi_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CqiRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CqiRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cqi_rel_canonical Job) (cqi_rel_surjective Job)). Qed.

Lemma cqi_reflexive (T : Type) rR rL (Hr : CqiRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cqi_transitive (T : Type) rR rL (Hr : CqiRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cqi_PR_JLFP_is_reflexive rR rL (Hr : CqiRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_reflexive Job dJ rL).
Proof. exact (cqi_reflexive Job rR rL Hr). Qed.

Lemma cqi_PR_JLFP_is_transitive rR rL (Hr : CqiRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_transitive Job dJ rL).
Proof. exact (cqi_transitive Job rR rL Hr). Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cqi_J_job_cost_positive cR cL (Hc : CqiParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

End JobDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

End UwlDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqiSchedRel Job sR sL.

Lemma cqi_UP_work_conserving aR aL (Ha : CqiParRel Job aR aL) cR cL (Hc : CqiParRel Job cR cL)
    arrR arrL (Harr : CqiArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.

(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section LBISvc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqiSchedRel Job sR sL.

End LBISvc.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LBIDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CqiParRel Job jaR jaL) (Hc : CqiParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CqiArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqiSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CqiRelRel Job hR hL.

Lemma cqi_LBI_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL).
Proof.
  apply: ct_forall_identity => j_hp.
  apply: ct_imp; first exact (cqi_arrives_in Job aR aL Ha j_hp).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_arrived_before Job jaR jaL Hja j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (cqi_US_completed_by Job sR sL Hs cR cL Hc j_hp tR tL Ht)).
Qed.

Notation QT := cqi_LBI_quiet_time.

Lemma cqi_not_quiet j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (~ @BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Not (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL)).
Proof. exact (ct_imp _ _ _ _ (QT j tR tL Ht) cqi_false_rel). Qed.

Lemma cqi_LBI_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyIntervalJLFP.busy_interval_prefix Job jaR cR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_prefix Job dJ jaL cL aL sL hL j t1L t2L).
Proof.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_and; first exact (QT j t1R t1L H1).
  apply: ct_and.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
    exact (cqi_not_quiet j tR tL Ht). }
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hja j)) (ct_decide_lt _ _ _ _ (Hja j) H2))).
Qed.

Lemma cqi_LP_work_conserving :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving jaR cR aR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job dJ jaL cL aL sL).
Proof. exact (cqi_UP_work_conserving Job sR sL Hs jaR jaL Hja cR cL Hc aR aL Ha). Qed.

End LBIDefs.

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section LPDPmRel.
Variable Job : eqType.
Definition CqiPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cqi_pm_canonical pR : CqiPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cqi_pm_surjective pL : CqiPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cqi_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CqiPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cqi_forall_cover _ _ CqiPmRel _ _ cqi_pm_canonical cqi_pm_surjective PR PL). Qed.

End LPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqiSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CqiPmRel Job pR pL.

Notation SA := (cqi_US_scheduled_at Job sR sL Hs).
Notation SV := (cqi_US_service Job sR sL Hs).

Lemma cqi_LPD_preemption_time tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (cqi_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR)
                        (match z with
                         | I.Option_some j => pL j (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL)
                         | I.Option_none => I.Bool_true end)) _).
  rewrite /LimitedPreemptionPlatform.preemption_time. destruct (sR tR) as [x|].
  - exact (Hp x _ _ (SV x tR tL Ht)).
  - exact (ct_bool_canonical true).
Qed.

Lemma cqi_LPD_not_preemptive_implies_scheduled j :
  PropSPropRel (LimitedPreemptionPlatform.not_preemptive_implies_scheduled sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_not_preemptive_implies_scheduled Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hp j _ _ (SV j tR tL Ht)))).
  exact (ct_bool_truth _ _ (SA j tR tL Ht)).
Qed.

Lemma cqi_LPD_execution_starts_with_preemption_point j :
  PropSPropRel (LimitedPreemptionPlatform.execution_starts_with_preemption_point sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_execution_starts_with_preemption_point Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  have Ht1 := cqi_succ_rel _ _ Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (SA j tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j _ _ Ht1)).
  exact (ct_bool_truth _ _ (Hp j _ _ (SV j _ _ Ht1))).
Qed.

Lemma cqi_LPD_correct_preemption_model arrR arrL (Harr : CqiArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.correct_preemption_model arrR sR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_correct_preemption_model Job dJ arrL sL pL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cqi_LPD_not_preemptive_implies_scheduled j).
  exact (cqi_LPD_execution_starts_with_preemption_point j).
Qed.

End LPDDefs.

Section LPDDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CqiPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CqiParRel Job cR cL) (Hm : CqiParRel Job mR mL) (Htm : CqiParRel Task tmR tmL).

Lemma cqi_LPD_job_cannot_become_nonpreemptive_before_execution j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution Job dJ pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (sub_nat_rel_canonical 0))). Qed.

Lemma cqi_LPD_job_cannot_be_nonpreemptive_after_completion j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion cR pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion Job dJ cL pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (Hc j))). Qed.

Lemma cqi_LPD_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (job_task : Job -> Task)
    arrR arrL (Harr : CqiArrRel Job arrR arrL) j :
  PropSPropRel (LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR mR tmR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment Task dT Job dJ job_task arrL mL tmL j).
Proof.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_le_correspondence _ _ _ _ (Hm j) (Htm (job_task j))).
Qed.

Lemma cqi_LPD_nonpreemptive_regions_have_bounded_length j :
  PropSPropRel (LimitedPreemptionPlatform.nonpreemptive_regions_have_bounded_length cR pR mR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length Job dJ cL pL mL j).
Proof.
  apply: ct_forall_nat => gR gL Hg.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (sub_nat_rel_canonical 0) Hg) (ct_decide_le _ _ _ _ Hg (Hc j)))).
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Hg Hx)
             (ct_decide_le _ _ _ _ Hx (sub_add_correspondence _ _ _ _ Hg (ct_sub_rel _ _ _ _ (Hm j) (sub_nat_rel_canonical 1)))))).
  - exact (ct_bool_truth _ _ (Hp j _ _ Hx)).
Qed.

Lemma cqi_LPD_model_with_bounded_nonpreemptive_segments (job_task : Job -> Task)
    arrR arrL (Harr : CqiArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments cR job_task arrR pR mR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments Task dT Job dJ cL job_task arrL pL mL tmL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cqi_LPD_job_cannot_become_nonpreemptive_before_execution j).
  apply: ct_and; first exact (cqi_LPD_job_cannot_be_nonpreemptive_after_completion j).
  apply: ct_and; first exact (cqi_LPD_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR arrL Harr j).
  exact (cqi_LPD_nonpreemptive_regions_have_bounded_length j).
Qed.

End LPDDefs2.

Lemma cqi_LPD_work_conserving (Job : eqType) sR sL (Hs : CqiSchedRel Job sR sL) cR cL (Hc : CqiParRel Job cR cL)
    c0R c0L (Hc0 : CqiParRel Job c0R c0L) arrR arrL (Harr : CqiArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving cR c0R arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job (ct_decidable_eq Job) cL c0L arrL sL).
Proof. exact (cqi_UP_work_conserving Job sR sL Hs cR cL Hc c0R c0L Hc0 arrR arrL Harr). Qed.

Section LPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqiSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CqiParRel Job aR aL) (Hc : CqiParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CqiArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CqiPmRel Job pR pL.

Lemma cqi_LPD_respects_JLFP_policy_at_preemption_point hR hL (Hh : CqiRelRel Job hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point aR cR arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point Job dJ aL cL arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_LPD_preemption_time Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh j_hp j)).
Qed.

End LPDResp.

(* ------------------------------------------------------------------ *)
(** * [\max] over a filtered sequence against the v0.6 [maxFiltered] (through the exported equation
    [maxFiltered_eq_foldr_cond]) *)

Section MaxSeq.
Variable X : Type.
Variables (PR : X -> bool) (PL : X -> I.Bool).
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).
Variables (FR : X -> nat) (FL : X -> Lean.Nat).
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cqi_foldr_max_cond : forall s : seq X,
  Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
              (I.List_map_inst2 X Lean.Nat (fun x => I.cond Lean.Nat (PL x) (FL x) (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)))
                 (cl_map cid s)))
           (sub_nat_to_imported (\max_(x <- s | PR x) FR x)).
Proof.
  elim => [|x s IH]; first by rewrite big_nil.
  rewrite big_cons.
  change (Logic.eq (I.Nat_max (I.cond Lean.Nat (PL x) (FL x) (sub_nat_to_imported 0))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
              (I.List_map_inst2 X Lean.Nat (fun x => I.cond Lean.Nat (PL x) (FL x) (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)))
                 (cl_map cid s))))
         (sub_nat_to_imported (if PR x then maxn (FR x) (\max_(j <- s | PR j) FR j) else \max_(j <- s | PR j) FR j))).
  rewrite IH (ct_bool_rel_logic _ _ (HP x)).
  have HFx := imported_eq_to_coq_eq _ _ (HF x).
  destruct (PR x).
  - change (Logic.eq (I.Nat_max (FL x) (sub_nat_to_imported (\max_(j <- s | PR j) FR j)))
                     (sub_nat_to_imported (maxn (FR x) (\max_(j <- s | PR j) FR j)))).
    rewrite -HFx. exact (ct_max_canonical _ _).
  - change (Logic.eq (I.Nat_max (sub_nat_to_imported 0) (sub_nat_to_imported (\max_(j <- s | PR j) FR j)))
                     (sub_nat_to_imported (\max_(j <- s | PR j) FR j))).
    rewrite (ct_max_canonical 0 _) max0n. reflexivity.
Qed.

Lemma cqi_max_filtered_rel s sL (Hs : ClListRel cid s sL) :
  SubNatRel (\max_(x <- s | PR x) FR x) (I.Prosa_Util_Sum_maxFiltered X sL PL FL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite -(imported_eq_to_coq_eq _ _ Hs).
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPriorityInversionBoundedInterface_maxFiltered_eq_foldr_cond X PL FL (cl_map cid s))).
  exact (Logic.eq_sym (cqi_foldr_max_cond s)).
Qed.

End MaxSeq.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem PriorityInversionIsBounded_max_length_of_priority_inversion_correspondence (Job : eqType) mR mL (Hm : CqiParRel Job mR mL)
    arrR arrL (Harr : CqiArrRel Job arrR arrL) hR hL (Hh : CqiRelRel Job hR hL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (@PriorityInversionIsBounded.max_length_of_priority_inversion Job mR arrR hR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_max_length_of_priority_inversion Job (ct_decidable_eq Job) mL arrL hL j tL).
Proof.
  exact (cqi_max_filtered_rel Job _ _ (fun x => ct_bool_not _ _ (Hh x j)) _ _ (fun x => ct_sub_rel _ _ _ _ (Hm x) (sub_nat_rel_canonical 1))
           _ _ (cqi_jobs_arrived_before Job arrR arrL Harr tR tL Ht)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point (Job : eqType) : Prop :=
  ltac:(type_of_term (@PriorityInversionIsBounded.not_quiet_implies_exists_scheduled_hp_job_at_preemption_point Job)).
Definition tgt_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point_correspondence (Job : eqType) :
  PropSPropRel (src_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point Job) (tgt_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point Job).
Proof.
  unfold src_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point, tgt_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => cR cL Hc.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqi_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (cqi_forall_rel Job) => hR hL Hh.
  apply: ct_imp; first exact (cqi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cqi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: (cqi_forall_pm Job) => pR pL Hp.
  apply: ct_imp; first exact (cqi_LPD_work_conserving Job sR sL Hs aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_respects_JLFP_policy_at_preemption_point Job sR sL Hs aR aL cR cL Ha Hc arrR arrL Harr pR pL Hp hR hL Hh).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqi_LBI_busy_interval_prefix Job aR aL cR cL Ha Hc arrR arrL Harr sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_LPD_preemption_time Job sR sL Hs pR pL Hp _ _ Ht)).
  apply: ct_exists_identity => j_hp.
  apply: ct_and; first exact (ct_bool_truth _ _ (cqi_arrived_between Job aR aL Ha j_hp _ _ _ _ H1 H2)).
  apply: ct_and; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
Qed.

Definition src_scheduling_of_any_segment_starts_with_preemption_time (Task Job : eqType) : Prop :=
  forall task_max_nps : Task -> Time.time,
    ltac:(type_of_term (@PriorityInversionIsBounded.scheduling_of_any_segment_starts_with_preemption_time Task task_max_nps Job)).
Definition tgt_scheduling_of_any_segment_starts_with_preemption_time (Task Job : eqType) : SProp :=
  forall task_max_nps : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_scheduling_of_any_segment_starts_with_preemption_time Task (ct_decidable_eq Task) task_max_nps Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_scheduling_of_any_segment_starts_with_preemption_time_correspondence (Task Job : eqType) :
  PropSPropRel (src_scheduling_of_any_segment_starts_with_preemption_time Task Job) (tgt_scheduling_of_any_segment_starts_with_preemption_time Task Job).
Proof.
  unfold src_scheduling_of_any_segment_starts_with_preemption_time, tgt_scheduling_of_any_segment_starts_with_preemption_time.
  apply: cqi_forall_par => tmR tmL Htm.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => mR mL Hm. apply: cqi_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: (cqi_forall_pm Job) => pR pL Hp.
  apply: ct_imp; first exact (cqi_LPD_correct_preemption_model Job sR sL Hs pR pL Hp arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_model_with_bounded_nonpreemptive_segments Task Job pR pL Hp cR cL mR mL tmR tmL Hc Hm Htm job_task arrR arrL Harr).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  apply: ct_exists_nat => pR' pL' Hp'.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (Ha j) Hp') (ct_decide_le _ _ _ _ Hp' Ht))).
  apply: ct_and; first exact (ct_bool_truth _ _ (cqi_LPD_preemption_time Job sR sL Hs pR pL Hp _ _ Hp')).
  apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Hp' Ht') (ct_decide_le _ _ _ _ Ht' Ht))).
  exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs j _ _ Ht')).
Qed.

Definition src_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point (Task Job : eqType) : Prop :=
  forall task_max_nps : Task -> Time.time,
    ltac:(type_of_term (@PriorityInversionIsBounded.not_quiet_implies_exists_scheduled_hp_job_after_preemption_point Task task_max_nps Job)).
Definition tgt_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point (Task Job : eqType) : SProp :=
  forall task_max_nps : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point Task (ct_decidable_eq Task) task_max_nps Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point_correspondence (Task Job : eqType) :
  PropSPropRel (src_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point Task Job) (tgt_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point Task Job).
Proof.
  unfold src_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point, tgt_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point.
  apply: cqi_forall_par => tmR tmL Htm.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => mR mL Hm. apply: cqi_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqi_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (cqi_forall_rel Job) => hR hL Hh.
  apply: ct_imp; first exact (cqi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cqi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: (cqi_forall_pm Job) => pR pL Hp.
  apply: ct_imp; first exact (cqi_LPD_correct_preemption_model Job sR sL Hs pR pL Hp arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_model_with_bounded_nonpreemptive_segments Task Job pR pL Hp cR cL mR mL tmR tmL Hc Hm Htm job_task arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_work_conserving Job sR sL Hs aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_respects_JLFP_policy_at_preemption_point Job sR sL Hs aR aL cR cL Ha Hc arrR arrL Harr pR pL Hp hR hL Hh).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqi_LBI_busy_interval_prefix Job aR aL cR cL Ha Hc arrR arrL Harr sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_forall_nat => tpR tpL Htp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_LPD_preemption_time Job sR sL Hs pR pL Hp _ _ Htp)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Htp) (ct_decide_lt _ _ _ _ Htp H2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Htp Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_exists_identity => j_hp.
  apply: ct_and; first exact (ct_bool_truth _ _ (cqi_arrived_between Job aR aL Ha j_hp _ _ _ _ H1 (cqi_succ_rel _ _ Ht))).
  apply: ct_and; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
Qed.

Definition src_not_quiet_implies_exists_scheduled_hp_job (Task Job : eqType) : Prop :=
  forall task_max_nps : Task -> Time.time,
    ltac:(type_of_term (@PriorityInversionIsBounded.not_quiet_implies_exists_scheduled_hp_job Task task_max_nps Job)).
Definition tgt_not_quiet_implies_exists_scheduled_hp_job (Task Job : eqType) : SProp :=
  forall task_max_nps : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_not_quiet_implies_exists_scheduled_hp_job Task (ct_decidable_eq Task) task_max_nps Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_not_quiet_implies_exists_scheduled_hp_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_not_quiet_implies_exists_scheduled_hp_job Task Job) (tgt_not_quiet_implies_exists_scheduled_hp_job Task Job).
Proof.
  unfold src_not_quiet_implies_exists_scheduled_hp_job, tgt_not_quiet_implies_exists_scheduled_hp_job.
  apply: cqi_forall_par => tmR tmL Htm.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => mR mL Hm. apply: cqi_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqi_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (cqi_forall_rel Job) => hR hL Hh.
  apply: ct_imp; first exact (cqi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cqi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: (cqi_forall_pm Job) => pR pL Hp.
  apply: ct_imp; first exact (cqi_LPD_correct_preemption_model Job sR sL Hs pR pL Hp arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_model_with_bounded_nonpreemptive_segments Task Job pR pL Hp cR cL mR mL tmR tmL Hc Hm Htm job_task arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_work_conserving Job sR sL Hs aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_respects_JLFP_policy_at_preemption_point Job sR sL Hs aR aL cR cL Ha Hc arrR arrL Harr pR pL Hp hR hL Hh).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqi_LBI_busy_interval_prefix Job aR aL cR cL Ha Hc arrR arrL Harr sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_forall_nat => KR KL HK.
  apply: ct_imp.
  { apply: ct_exists_nat => prR prL Hpr.
    apply: ct_and; first exact (ct_bool_truth _ _ (cqi_LPD_preemption_time Job sR sL Hs pR pL Hp _ _ Hpr)).
    exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Hpr) (ct_decide_le _ _ _ _ Hpr (sub_add_correspondence _ _ _ _ H1 HK)))). }
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ H1 HK) Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_exists_identity => j_hp.
  apply: ct_and; first exact (ct_bool_truth _ _ (cqi_arrived_between Job aR aL Ha j_hp _ _ _ _ H1 (cqi_succ_rel _ _ Ht))).
  apply: ct_and; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
Qed.

Definition src_hp_job_not_scheduled_before_quiet_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@PriorityInversionIsBounded.hp_job_not_scheduled_before_quiet_time Job)).
Definition tgt_hp_job_not_scheduled_before_quiet_time (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_hp_job_not_scheduled_before_quiet_time Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_hp_job_not_scheduled_before_quiet_time_correspondence (Job : eqType) :
  PropSPropRel (src_hp_job_not_scheduled_before_quiet_time Job) (tgt_hp_job_not_scheduled_before_quiet_time Job).
Proof.
  unfold src_hp_job_not_scheduled_before_quiet_time, tgt_hp_job_not_scheduled_before_quiet_time.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => cR cL Hc.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (cqi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_forall_identity => jhp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cqi_LBI_quiet_time Job aR aL cR cL Ha Hc arrR arrL Harr sR sL Hs hR hL Hh j _ _ (cqi_succ_rel _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs jhp _ _ (cqi_succ_rel _ _ Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hh jhp j)).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (cqi_US_scheduled_at Job sR sL Hs jhp tR tL Ht))).
Qed.

Definition src_low_priority_job_arrives_before_busy_interval_prefix (Task Job : eqType) : Prop :=
  forall task_max_nps : Task -> Time.time,
    ltac:(type_of_term (@PriorityInversionIsBounded.low_priority_job_arrives_before_busy_interval_prefix Task task_max_nps Job)).
Definition tgt_low_priority_job_arrives_before_busy_interval_prefix (Task Job : eqType) : SProp :=
  forall task_max_nps : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_low_priority_job_arrives_before_busy_interval_prefix Task (ct_decidable_eq Task) task_max_nps Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_low_priority_job_arrives_before_busy_interval_prefix_correspondence (Task Job : eqType) :
  PropSPropRel (src_low_priority_job_arrives_before_busy_interval_prefix Task Job) (tgt_low_priority_job_arrives_before_busy_interval_prefix Task Job).
Proof.
  unfold src_low_priority_job_arrives_before_busy_interval_prefix, tgt_low_priority_job_arrives_before_busy_interval_prefix.
  apply: cqi_forall_par => tmR tmL Htm.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => mR mL Hm. apply: cqi_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqi_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (cqi_forall_rel Job) => hR hL Hh.
  apply: ct_imp; first exact (cqi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cqi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: (cqi_forall_pm Job) => pR pL Hp.
  apply: ct_imp; first exact (cqi_LPD_correct_preemption_model Job sR sL Hs pR pL Hp arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_model_with_bounded_nonpreemptive_segments Task Job pR pL Hp cR cL mR mL tmR tmL Hc Hm Htm job_task arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_work_conserving Job sR sL Hs aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_respects_JLFP_policy_at_preemption_point Job sR sL Hs aR aL cR cL Ha Hc arrR arrL Harr pR pL Hp hR hL Hh).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqi_LBI_busy_interval_prefix Job aR aL cR cL Ha Hc arrR arrL Harr sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_forall_identity => jlp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs jlp tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hh jlp j))).
  exact (sub_nat_lt_correspondence _ _ _ _ (Ha jlp) H1).
Qed.

Definition src_low_priority_job_scheduled_before_busy_interval_prefix (Task Job : eqType) : Prop :=
  forall task_max_nps : Task -> Time.time,
    ltac:(type_of_term (@PriorityInversionIsBounded.low_priority_job_scheduled_before_busy_interval_prefix Task task_max_nps Job)).
Definition tgt_low_priority_job_scheduled_before_busy_interval_prefix (Task Job : eqType) : SProp :=
  forall task_max_nps : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_low_priority_job_scheduled_before_busy_interval_prefix Task (ct_decidable_eq Task) task_max_nps Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_low_priority_job_scheduled_before_busy_interval_prefix_correspondence (Task Job : eqType) :
  PropSPropRel (src_low_priority_job_scheduled_before_busy_interval_prefix Task Job) (tgt_low_priority_job_scheduled_before_busy_interval_prefix Task Job).
Proof.
  unfold src_low_priority_job_scheduled_before_busy_interval_prefix, tgt_low_priority_job_scheduled_before_busy_interval_prefix.
  apply: cqi_forall_par => tmR tmL Htm.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => mR mL Hm. apply: cqi_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqi_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (cqi_forall_rel Job) => hR hL Hh.
  apply: ct_imp; first exact (cqi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cqi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: (cqi_forall_pm Job) => pR pL Hp.
  apply: ct_imp; first exact (cqi_LPD_correct_preemption_model Job sR sL Hs pR pL Hp arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_model_with_bounded_nonpreemptive_segments Task Job pR pL Hp cR cL mR mL tmR tmL Hc Hm Htm job_task arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_work_conserving Job sR sL Hs aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_respects_JLFP_policy_at_preemption_point Job sR sL Hs aR aL cR cL Ha Hc arrR arrL Harr pR pL Hp hR hL Hh).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqi_LBI_busy_interval_prefix Job aR aL cR cL Ha Hc arrR arrL Harr sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_forall_identity => jlp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs jlp tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hh jlp j))).
  apply: ct_exists_nat => t'R t'L Ht'.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Ht' H1).
  exact (ct_bool_truth _ _ (cqi_US_scheduled_at Job sR sL Hs jlp _ _ Ht')).
Qed.

Definition src_preemption_time_exists (Task Job : eqType) : Prop :=
  forall task_max_nps : Task -> Time.time,
    ltac:(type_of_term (@PriorityInversionIsBounded.preemption_time_exists Task task_max_nps Job)).
Definition tgt_preemption_time_exists (Task Job : eqType) : SProp :=
  forall task_max_nps : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_preemption_time_exists Task (ct_decidable_eq Task) task_max_nps Job (ct_decidable_eq Job))).
Theorem PriorityInversionIsBounded_preemption_time_exists_correspondence (Task Job : eqType) :
  PropSPropRel (src_preemption_time_exists Task Job) (tgt_preemption_time_exists Task Job).
Proof.
  unfold src_preemption_time_exists, tgt_preemption_time_exists.
  apply: cqi_forall_par => tmR tmL Htm.
  apply: cqi_forall_par => aR aL Ha. apply: cqi_forall_par => mR mL Hm. apply: cqi_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqi_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqi_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqi_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (cqi_forall_rel Job) => hR hL Hh.
  apply: ct_imp; first exact (cqi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cqi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: (cqi_forall_pm Job) => pR pL Hp.
  apply: ct_imp; first exact (cqi_LPD_correct_preemption_model Job sR sL Hs pR pL Hp arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_model_with_bounded_nonpreemptive_segments Task Job pR pL Hp cR cL mR mL tmR tmL Hc Hm Htm job_task arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_work_conserving Job sR sL Hs aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (cqi_LPD_respects_JLFP_policy_at_preemption_point Job sR sL Hs aR aL cR cL Ha Hc arrR arrL Harr pR pL Hp hR hL Hh).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqi_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqi_LBI_busy_interval_prefix Job aR aL cR cL Ha Hc arrR arrL Harr sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_exists_nat => prR prL Hpr.
  apply: ct_and; first exact (ct_bool_truth _ _ (cqi_LPD_preemption_time Job sR sL Hs pR pL Hp _ _ Hpr)).
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Hpr) (ct_decide_le _ _ _ _ Hpr (sub_add_correspondence _ _ _ _ H1 (PriorityInversionIsBounded_max_length_of_priority_inversion_correspondence Job mR mL Hm arrR arrL Harr hR hL Hh j _ _ H1))))).
Qed.
