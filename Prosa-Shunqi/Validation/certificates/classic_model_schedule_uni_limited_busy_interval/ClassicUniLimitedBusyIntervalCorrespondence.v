From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.list classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.basic.platform classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.busy_interval.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniLimitedBusyInterval.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniLimitedBusyIntervalBase ClassicUniLimitedBusyIntervalList.

Module I := ImportedClassicUniLimitedBusyInterval.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/busy_interval.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the eqTypes'
    decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters pointwise
    through [SubNatRel]; arrival sequences pointwise on related times; JLFP policies pointwise on Booleans; uniprocessor
    schedules pointwise through the option map; all with two-way totals.  The service, workload, arrival, job, schedule
    and platform notions as in the accepted classic certificates (re-bound below); [cumulative_priority_inversion]
    through a kernel-guarded [rfl] body projection; [a ==> b] against [!a || b]; the informative reflection
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

Lemma clb_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma clb_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma clb_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) clb_false_rel). Qed.

Lemma clb_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma clb_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma clb_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma clb_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma clb_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma clb_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (clb_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => clb_unmap_rel T l) PR PL).
Qed.

Definition ClbParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma clb_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, ClbParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (clb_forall_cover _ _ (ClbParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint clb_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (clb_natl s') end.

Definition clb_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma clb_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) clb_one) (clb_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) clb_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (clb_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma clb_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (clb_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (clb_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma clb_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma clb_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma clb_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma clb_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH clb_cl_append. reflexivity.
Qed.

Lemma clb_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition ClbFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma clb_bigcat_rel (A : Type) fR fL (Hf : ClbFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicUniLimitedBusyIntervalInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (clb_iota_range (nR - mR) 0) clb_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (clb_cl_map_ext _ _ Hpt) (clb_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) clb_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite clb_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition ClbArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition clb_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition clb_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma clb_arr_canonical aR : ClbArrRel aR (clb_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /clb_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma clb_arr_surjective aL : ClbArrRel (clb_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma clb_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, ClbArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (clb_forall_cover _ _ ClbArrRel clb_arr_to_target clb_arr_to_source clb_arr_canonical clb_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma clb_jobs_arrived_between aR aL (Ha : ClbArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (clb_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma clb_arrives_in aR aL (Ha : ClbArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (clb_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma clb_consistent pR pL (Hp : ClbParRel Job pR pL) aR aL (Ha : ClbArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (clb_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma clb_is_a_set aR aL (Ha : ClbArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (clb_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma clb_jobs_arrived_before aR aL (Ha : ClbArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (clb_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma clb_arrives_at aR aL (Ha : ClbArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (clb_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma clb_has_arrived pR pL (Hp : ClbParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma clb_arrived_before pR pL (Hp : ClbParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

Lemma clb_arrived_between pR pL (Hp : ClbParRel Job pR pL) j t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  CtBoolRel (ArrivalSequence.arrived_between pR j t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_between Job dJ pL j t1L t2L).
Proof. exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hp j)) (ct_decide_lt _ _ _ _ (Hp j) H2)). Qed.

End ArrivalDefs2.

Fixpoint clb_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (clb_snatl s') end.

Lemma clb_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (clb_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (clb_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma clb_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (clb_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (clb_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma clb_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition ClbFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma clb_fun_canonical FR FL (HF : ClbFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma clb_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma clb_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : ClbFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := clb_nat_sub_canonical nR mR.
  rewrite clb_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (clb_foldr_add FL FR (clb_fun_canonical FR FL HF)).
  by rewrite clb_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition clb_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition clb_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma clb_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma clb_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (clb_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition ClbSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition clb_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition clb_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma clb_sched_canonical sR : ClbSchedRel sR (clb_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /clb_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma clb_sched_surjective sL : ClbSchedRel (clb_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /clb_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma clb_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, ClbSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (clb_forall_cover _ _ ClbSchedRel clb_sched_to_target clb_sched_to_source clb_sched_canonical clb_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma clb_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, ClbSchedRel Job sR (clb_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), ClbSchedRel Job (clb_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (clb_sched_canonical Job) (clb_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClbSchedRel Job sR sL.

Lemma clb_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (clb_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (clb_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma clb_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (clb_US_scheduled_at j tR tL Ht)). Qed.

Lemma clb_service_at_fun j : ClbFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (clb_US_service_at j kR kL Hk). Qed.

Lemma clb_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (clb_ico _ _ _ _ _ _ H1 H2 (clb_service_at_fun j)). Qed.

Lemma clb_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (clb_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma clb_US_completed_by cR cL (Hc : ClbParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (clb_US_service j tR tL Ht)). Qed.

Lemma clb_US_pending aR aL (Ha : ClbParRel Job aR aL) cR cL (Hc : ClbParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (clb_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (clb_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma clb_US_backlogged aR aL (Ha : ClbParRel Job aR aL) cR cL (Hc : ClbParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (clb_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (clb_US_scheduled_at j tR tL Ht))).
Qed.

Lemma clb_US_is_idle tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.is_idle sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_is_idle Job dJ sL tL).
Proof.
  apply: ct_decide_bool.
  exact (clb_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == None) (Lean.eq z (cl_opt None)))
           (clb_opt_eqb_rel Job (sR tR) None)).
Qed.

Lemma clb_busy_fun : ClbFunRel (fun t => nat_of_bool (~~ UniprocessorSchedule.is_idle sR t))
    (fun t => I.Bool_toNat (I.Bool_not (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_is_idle Job dJ sL t))).
Proof. intros kR kL Hk. exact (ct_bool_to_nat _ _ (ct_bool_not _ _ (clb_US_is_idle kR kL Hk))). Qed.

Lemma clb_US_jobs_come_from_arrival_sequence arrR arrL (Harr : ClbArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_US_scheduled_at j tR tL Ht)).
  exact (clb_arrives_in Job arrR arrL Harr j).
Qed.

Lemma clb_US_jobs_must_arrive_to_execute aR aL (Ha : ClbParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (clb_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma clb_US_completed_jobs_dont_execute cR cL (Hc : ClbParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (clb_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma clb_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniLimitedBusyIntervalInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicUniLimitedBusyIntervalInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma clb_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (clb_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma clb_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniLimitedBusyIntervalInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniLimitedBusyIntervalInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniLimitedBusyIntervalInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma clb_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (clb_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition ClbPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma clb_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, ClbPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (clb_forall_cover _ _ (ClbPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition ClbRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma clb_rel_canonical (T : Type) (rR : T -> T -> bool) : ClbRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma clb_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : ClbRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma clb_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, ClbRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (clb_forall_cover _ _ (ClbRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (clb_rel_canonical T) (clb_rel_surjective T) PR PL).
Qed.

Definition ClbJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClbRelRel T (rR tR) (rL tL).

Lemma clb_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  ClbJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma clb_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  ClbJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma clb_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, ClbJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (clb_forall_cover _ _ (ClbJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (clb_jldp_canonical T) (clb_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma clb_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, ClbRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, ClbRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (clb_rel_canonical Task) (clb_rel_surjective Task)). Qed.

Lemma clb_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, ClbRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, ClbRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (clb_rel_canonical Job) (clb_rel_surjective Job)). Qed.

Lemma clb_reflexive (T : Type) rR rL (Hr : ClbRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma clb_PR_FP_is_reflexive rR rL (Hr : ClbRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (clb_reflexive Task rR rL Hr). Qed.

Lemma clb_PR_JLFP_is_reflexive rR rL (Hr : ClbRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_reflexive Job dJ rL).
Proof. exact (clb_reflexive Job rR rL Hr). Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma clb_J_job_cost_positive cR cL (Hc : ClbParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

End JobDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma clb_WL_workload_of_jobs cR cL (Hc : ClbParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : ClbPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (clb_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

Lemma clb_WL_workload_of_higher_or_equal_priority_jobs cR cL (Hc : ClbParRel Job cR cL)
    jobsR jobsL (Hj : ClListRel cid jobsR jobsL) hR hL (Hh : ClbRelRel Job hR hL) j :
  SubNatRel (Workload.workload_of_higher_or_equal_priority_jobs cR jobsR hR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_higher_or_equal_priority_jobs Job dJ cL jobsL hL j).
Proof. exact (clb_WL_workload_of_jobs cR cL Hc jobsR jobsL Hj _ _ (fun j_hp => Hh j_hp j)). Qed.

End UwlDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClbSchedRel Job sR sL.

Lemma clb_UP_work_conserving aR aL (Ha : ClbParRel Job aR aL) cR cL (Hc : ClbParRel Job cR cL)
    arrR arrL (Harr : ClbArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (clb_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (clb_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.



(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section Svc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClbSchedRel Job sR sL.

Lemma clb_service_of_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : ClbPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (clb_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => clb_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

Lemma clb_service_of_hep_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    hR hL (Hh : ClbRelRel Job hR hL) j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_higher_or_equal_priority_jobs sR jobsR hR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_higher_or_equal_priority_jobs Job dJ sL jobsL hL j t1L t2L).
Proof. exact (clb_service_of_jobs _ _ Hj _ _ (fun j_hp => Hh j_hp j) _ _ H1 _ _ H2). Qed.
End Svc.


(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

Lemma clb_implb aR aL (Ha : CtBoolRel aR aL) bR bL (Hb : CtBoolRel bR bL) :
  CtBoolRel (aR ==> bR) (I.Bool_or (I.Bool_not aL) bL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite (ct_bool_rel_logic _ _ Ha) (ct_bool_rel_logic _ _ Hb). clear Ha Hb.
  by case: aR; case: bR.
Qed.

(** Informative reflections: constructor-preserving maps in both directions (as in the accepted classic record
    certificates). *)
Definition clb_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    reflect PR bR -> I.Prosa_Classic_Util_List_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isTrue PL (prop_to_sprop _ _ HP Htrue)).
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isFalse PL
      (fun HL => ct_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition clb_reflect_backward_at_bool (PR : Prop) (PL : SProp) (HP : PropSPropRel PR PL) (bL : I.Bool) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR (ct_l2b bL) :=
  fun HL =>
    match HL in I.Prosa_Classic_Util_List_BoolReflect _ b return reflect PR (ct_l2b b) with
    | I.Prosa_Classic_Util_List_BoolReflect_isTrue Htrue => ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | I.Prosa_Classic_Util_List_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR => interpret_strict Logic.False
          (ct_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition clb_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR bR.
Proof. destruct Hb. destruct bR; cbn; exact (clb_reflect_backward_at_bool PR PL HP _). Defined.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : ClbParRel Job jaR jaL) (Hc : ClbParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : ClbArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClbSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : ClbRelRel Job hR hL.

Theorem BusyIntervalJLFP_quiet_time_correspondence j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL).
Proof.
  apply: ct_forall_identity => j_hp.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j_hp).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_arrived_before Job jaR jaL Hja j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (clb_US_completed_by Job sR sL Hs cR cL Hc j_hp tR tL Ht)).
Qed.

Notation QT := BusyIntervalJLFP_quiet_time_correspondence.

Lemma clb_not_quiet j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (~ @BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Not (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL)).
Proof. exact (ct_imp _ _ _ _ (QT j tR tL Ht) clb_false_rel). Qed.

Theorem BusyIntervalJLFP_busy_interval_prefix_correspondence j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyIntervalJLFP.busy_interval_prefix Job jaR cR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_prefix Job dJ jaL cL aL sL hL j t1L t2L).
Proof.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_and; first exact (QT j t1R t1L H1).
  apply: ct_and.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
    exact (clb_not_quiet j tR tL Ht). }
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hja j)) (ct_decide_lt _ _ _ _ (Hja j) H2))).
Qed.

Theorem BusyIntervalJLFP_busy_interval_correspondence j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyIntervalJLFP.busy_interval Job jaR cR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval Job dJ jaL cL aL sL hL j t1L t2L).
Proof. exact (ct_and _ _ _ _ (BusyIntervalJLFP_busy_interval_prefix_correspondence j t1R t1L H1 t2R t2L H2) (QT j t2R t2L H2)). Qed.

Theorem BusyIntervalJLFP_is_priority_inversion_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@BusyIntervalJLFP.is_priority_inversion Job sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion Job dJ sL hL j tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /BusyIntervalJLFP.is_priority_inversion. unfold I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion.
  rewrite -(imported_eq_to_coq_eq _ _ (Hs tR tL Ht)).
  case: (sR tR) => [jlp|]; last reflexivity.
  cbn. rewrite (ct_bool_rel_logic _ _ (Hh jlp j)). by case: (hR jlp j).
Qed.

Theorem BusyIntervalJLFP_cumulative_priority_inversion_correspondence j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@BusyIntervalJLFP.cumulative_priority_inversion Job sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_cumulative_priority_inversion Job dJ sL hL j t1L t2L).
Proof.
  exact (clb_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (BusyIntervalJLFP_is_priority_inversion_correspondence j kR kL Hk))).
Qed.

Theorem BusyIntervalJLFP_priority_inversion_of_job_is_bounded_by_correspondence j BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (@BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by Job jaR cR aR sR hR j BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_priority_inversion_of_job_is_bounded_by Job dJ jaL cL aL sL hL j BL).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (BusyIntervalJLFP_busy_interval_prefix_correspondence j t1R t1L H1 t2R t2L H2).
  exact (sub_nat_le_correspondence _ _ _ _ (BusyIntervalJLFP_cumulative_priority_inversion_correspondence j t1R t1L H1 t2R t2L H2) HB).
Qed.

Theorem BusyIntervalJLFP_priority_inversion_is_bounded_by_correspondence (Task : eqType) (job_task : Job -> Task) tsk BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (@BusyIntervalJLFP.priority_inversion_is_bounded_by Task Job jaR cR job_task aR sR hR tsk BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_priority_inversion_is_bounded_by Task (ct_decidable_eq Task) Job dJ jaL cL job_task aL sL hL tsk BL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  exact (BusyIntervalJLFP_priority_inversion_of_job_is_bounded_by_correspondence j BR BL HB).
Qed.

Theorem BusyIntervalJLFP_quiet_time_dec_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@BusyIntervalJLFP.quiet_time_dec Job cR aR sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time_dec Job dJ cL aL sL hL j tL).
Proof.
  rewrite /BusyIntervalJLFP.quiet_time_dec. unfold I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time_dec.
  refine (clb_trs (clb_jobs_arrived_before Job aR aL Ha tR tL Ht) (fun z => CtBoolRel _ (I.List_all Job z _)) _).
  apply: cl_all => j_hp.
  exact (clb_implb _ _ (Hh j_hp j) _ _ (clb_US_completed_by Job sR sL Hs cR cL Hc j_hp tR tL Ht)).
Qed.

Theorem BusyIntervalJLFP_no_carry_in_correspondence tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@BusyIntervalJLFP.no_carry_in Job jaR cR aR sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_no_carry_in Job dJ jaL cL aL sL tL).
Proof.
  apply: ct_forall_identity => j_o.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j_o).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_arrived_before Job jaR jaL Hja j_o tR tL Ht)).
  exact (ct_bool_truth _ _ (clb_US_completed_by Job sR sL Hs cR cL Hc j_o tR tL Ht)).
Qed.

Lemma clb_LP_work_conserving :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving jaR cR aR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job dJ jaL cL aL sL).
Proof. exact (clb_UP_work_conserving Job sR sL Hs jaR jaL Hja cR cL Hc aR aL Ha). Qed.
End Defs.

Notation QTc := BusyIntervalJLFP_quiet_time_correspondence.
Notation NQc := clb_not_quiet.
Notation BPc := BusyIntervalJLFP_busy_interval_prefix_correspondence.
Notation BIc := BusyIntervalJLFP_busy_interval_correspondence.
Notation PIc := BusyIntervalJLFP_priority_inversion_of_job_is_bounded_by_correspondence.
Notation QDc := BusyIntervalJLFP_quiet_time_dec_correspondence.
Notation NCc := BusyIntervalJLFP_no_carry_in_correspondence.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** [quiet_time_P] is an informative reflection (a [reflect] value); it is related by constructor-preserving maps in
    both directions, at related inputs obtained from the two-way totals of every input relation. *)
Definition src_quiet_time_P (Job : eqType) : Type := ltac:(let X := type of (@BusyIntervalJLFP.quiet_time_P Job) in exact X).
Definition tgt_quiet_time_P (Job : eqType) : Type := ltac:(let X := type of (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time_P Job (ct_decidable_eq Job)) in exact X).

Theorem BusyIntervalJLFP_quiet_time_P_correspondence (Job : eqType) :
  Datatypes.prod (src_quiet_time_P Job -> tgt_quiet_time_P Job) (tgt_quiet_time_P Job -> src_quiet_time_P Job).
Proof.
  unfold src_quiet_time_P, tgt_quiet_time_P. split.
  - intros f jaL cL aL HconsL sL hL j tL.
    pose jaR := fun x => sub_nat_to_rocq (jaL x). pose cR := fun x => sub_nat_to_rocq (cL x).
    have Hja : ClbParRel Job jaR jaL := fun x => sub_nat_rel_surjective (jaL x).
    have Hc : ClbParRel Job cR cL := fun x => sub_nat_rel_surjective (cL x).
    have Ha := clb_arr_surjective Job aL. have Hs := clb_sched_surjective Job sL. have Hh := clb_rel_surjective Job hL.
    have Ht := sub_nat_rel_surjective tL.
    have HconsR := sprop_to_prop _ _ (clb_consistent Job jaR jaL Hja _ _ Ha) HconsL.
    exact (clb_reflect_forward _ _ _ _ (QTc Job jaR jaL cR cL Hja Hc _ _ Ha _ _ Hs _ _ Hh j _ _ Ht)
             (QDc Job cR cL Hc _ _ Ha _ _ Hs _ _ Hh j _ _ Ht) (f jaR cR _ HconsR _ _ j _)).
  - intros g jaR cR aR HconsR sR hR j tR.
    have Hja : ClbParRel Job jaR (fun x => sub_nat_to_imported (jaR x)) := fun x => sub_nat_rel_canonical (jaR x).
    have Hc : ClbParRel Job cR (fun x => sub_nat_to_imported (cR x)) := fun x => sub_nat_rel_canonical (cR x).
    have Ha := clb_arr_canonical Job aR. have Hs := clb_sched_canonical Job sR. have Hh := clb_rel_canonical Job hR.
    have Ht := sub_nat_rel_canonical tR.
    have HconsL := prop_to_sprop _ _ (clb_consistent Job jaR _ Hja _ _ Ha) HconsR.
    exact (clb_reflect_backward _ _ _ _ (QTc Job jaR _ cR _ Hja Hc _ _ Ha _ _ Hs _ _ Hh j _ _ Ht)
             (QDc Job cR _ Hc _ _ Ha _ _ Hs _ _ Hh j _ _ Ht) (g _ _ _ HconsL _ _ j _)).
Qed.

Definition src_job_completes_within_busy_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.job_completes_within_busy_interval Job)).
Definition tgt_job_completes_within_busy_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_job_completes_within_busy_interval Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_job_completes_within_busy_interval_correspondence (Job : eqType) :
  PropSPropRel (src_job_completes_within_busy_interval Job) (tgt_job_completes_within_busy_interval Job).
Proof.
  unfold src_job_completes_within_busy_interval, tgt_job_completes_within_busy_interval.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (clb_PR_FP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_forall_nat => t2R t2L Ht2.
  apply: ct_imp; first exact ((BIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ Ht2)).
  exact (ct_bool_truth _ _ (clb_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht2)).
Qed.

Definition src_not_quiet_implies_exists_pending_job (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.not_quiet_implies_exists_pending_job Job)).
Definition tgt_not_quiet_implies_exists_pending_job (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_not_quiet_implies_exists_pending_job Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_not_quiet_implies_exists_pending_job_correspondence (Job : eqType) :
  PropSPropRel (src_not_quiet_implies_exists_pending_job Job) (tgt_not_quiet_implies_exists_pending_job Job).
Proof.
  unfold src_not_quiet_implies_exists_pending_job, tgt_not_quiet_implies_exists_pending_job.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_forall_nat => t2R t2L Ht2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2).
  apply: ct_imp; first exact (QTc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1).
  apply: ct_imp; first exact (NQc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht2).
  apply: ct_exists_identity => j_hp.
  apply: ct_and; first exact (clb_arrives_in Job aR aL Ha j_hp).
  apply: ct_and; first exact (ct_bool_truth _ _ (clb_arrived_between Job jaR jaL Hja j_hp _ _ _ _ Ht1 Ht2)).
  apply: ct_and; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (clb_US_completed_by Job sR sL Hs cR cL Hc j_hp _ _ Ht2)) clb_false_rel).
Qed.

Definition src_idle_time_implies_quiet_time_at_the_next_time_instant (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.idle_time_implies_quiet_time_at_the_next_time_instant Job)).
Definition tgt_idle_time_implies_quiet_time_at_the_next_time_instant (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_idle_time_implies_quiet_time_at_the_next_time_instant Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_idle_time_implies_quiet_time_at_the_next_time_instant_correspondence (Job : eqType) :
  PropSPropRel (src_idle_time_implies_quiet_time_at_the_next_time_instant Job) (tgt_idle_time_implies_quiet_time_at_the_next_time_instant Job).
Proof.
  unfold src_idle_time_implies_quiet_time_at_the_next_time_instant, tgt_idle_time_implies_quiet_time_at_the_next_time_instant.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_US_is_idle Job sR sL Hs tR tL Ht)).
  exact (QTc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ (clb_succ_rel _ _ Ht)).
Qed.

Definition src_pending_hp_job_exists (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.pending_hp_job_exists Job)).
Definition tgt_pending_hp_job_exists (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_pending_hp_job_exists Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_pending_hp_job_exists_correspondence (Job : eqType) :
  PropSPropRel (src_pending_hp_job_exists Job) (tgt_pending_hp_job_exists Job).
Proof.
  unfold src_pending_hp_job_exists, tgt_pending_hp_job_exists.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_forall_nat => t2R t2L Ht2.
  apply: ct_imp; first exact ((BPc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ Ht2)).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ht1 Ht) (ct_decide_lt _ _ _ _ Ht Ht2))).
  apply: ct_exists_identity => jhp.
  apply: ct_and; first exact (clb_arrives_in Job aR aL Ha jhp).
  apply: ct_and; first exact (ct_bool_truth _ _ (clb_US_pending Job sR sL Hs jaR jaL Hja cR cL Hc jhp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh jhp j)).
Qed.

Definition src_not_quiet_implies_not_idle (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.not_quiet_implies_not_idle Job)).
Definition tgt_not_quiet_implies_not_idle (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_not_quiet_implies_not_idle Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_not_quiet_implies_not_idle_correspondence (Job : eqType) :
  PropSPropRel (src_not_quiet_implies_not_idle Job) (tgt_not_quiet_implies_not_idle Job).
Proof.
  unfold src_not_quiet_implies_not_idle, tgt_not_quiet_implies_not_idle.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_forall_nat => t2R t2L Ht2.
  apply: ct_imp; first exact ((BPc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ Ht2)).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ht1 Ht) (ct_decide_lt _ _ _ _ Ht Ht2))).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (clb_US_is_idle Job sR sL Hs tR tL Ht)) clb_false_rel).
Qed.

Definition src_hep_jobs_receive_no_service_before_quiet_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.hep_jobs_receive_no_service_before_quiet_time Job)).
Definition tgt_hep_jobs_receive_no_service_before_quiet_time (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_hep_jobs_receive_no_service_before_quiet_time Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_hep_jobs_receive_no_service_before_quiet_time_correspondence (Job : eqType) :
  PropSPropRel (src_hep_jobs_receive_no_service_before_quiet_time Job) (tgt_hep_jobs_receive_no_service_before_quiet_time Job).
Proof.
  unfold src_hep_jobs_receive_no_service_before_quiet_time, tgt_hep_jobs_receive_no_service_before_quiet_time.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_imp; first exact (QTc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1).
  apply: ct_forall_nat => dlR dlL Hdl.
  exact (sub_nat_eq_correspondence _ _ _ _ (clb_service_of_hep_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j _ _ Ht1 _ _ (sub_add_correspondence _ _ _ _ Ht1 Hdl)) (clb_service_of_hep_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ (sub_nat_rel_canonical 0) (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j _ _ Ht1 _ _ (sub_add_correspondence _ _ _ _ Ht1 Hdl))).
Qed.

Definition src_no_idle_time_within_non_quiet_time_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.no_idle_time_within_non_quiet_time_interval Job)).
Definition tgt_no_idle_time_within_non_quiet_time_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_no_idle_time_within_non_quiet_time_interval Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_no_idle_time_within_non_quiet_time_interval_correspondence (Job : eqType) :
  PropSPropRel (src_no_idle_time_within_non_quiet_time_interval Job) (tgt_no_idle_time_within_non_quiet_time_interval Job).
Proof.
  unfold src_no_idle_time_within_non_quiet_time_interval, tgt_no_idle_time_within_non_quiet_time_interval.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ Ht1 Ht) (ct_decide_le _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht1 Hdl)))).
    exact (NQc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  exact (sub_nat_eq_correspondence _ _ _ _ (clb_service_of_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ (sub_nat_rel_canonical 0) (sub_add_correspondence _ _ _ _ Ht1 Hdl)) _ _ (fun _ => ct_bool_canonical true) _ _ Ht1 _ _ (sub_add_correspondence _ _ _ _ Ht1 Hdl)) Hdl).
Qed.

Definition src_exists_busy_interval_prefix (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.exists_busy_interval_prefix Job)).
Definition tgt_exists_busy_interval_prefix (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_exists_busy_interval_prefix Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_exists_busy_interval_prefix_correspondence (Job : eqType) :
  PropSPropRel (src_exists_busy_interval_prefix Job) (tgt_exists_busy_interval_prefix Job).
Proof.
  unfold src_exists_busy_interval_prefix, tgt_exists_busy_interval_prefix.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (clb_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => tbR tbL Htb.
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_US_pending Job sR sL Hs jaR jaL Hja cR cL Hc j tbR tbL Htb)).
  apply: ct_exists_nat => t1R t1L Ht1.
  apply: ct_and; first exact (BPc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ (clb_succ_rel _ _ Htb)).
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ht1 (Hja j)) (ct_decide_le _ _ _ _ (Hja j) Htb))).
Qed.

Definition src_busy_interval_has_uninterrupted_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.busy_interval_has_uninterrupted_service Job)).
Definition tgt_busy_interval_has_uninterrupted_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_has_uninterrupted_service Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_busy_interval_has_uninterrupted_service_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_has_uninterrupted_service Job) (tgt_busy_interval_has_uninterrupted_service Job).
Proof.
  unfold src_busy_interval_has_uninterrupted_service, tgt_busy_interval_has_uninterrupted_service.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_forall_nat => tbR tbL Htb.
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_imp; first exact ((BPc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ (clb_succ_rel _ _ Htb))).
  apply: ct_forall_nat => pbR pbL Hpb.
  apply: ct_imp; first exact (PIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Hpb).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ Ht1 Ht) (ct_decide_le _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht1 Hdl)))).
    exact (NQc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  exact (sub_nat_le_correspondence _ _ _ _ Hdl (sub_add_correspondence _ _ _ _ Hpb (clb_service_of_hep_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j _ _ Ht1 _ _ (sub_add_correspondence _ _ _ _ Ht1 Hdl)))).
Qed.

Definition src_busy_interval_too_much_workload (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.busy_interval_too_much_workload Job)).
Definition tgt_busy_interval_too_much_workload (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_too_much_workload Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_busy_interval_too_much_workload_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_too_much_workload Job) (tgt_busy_interval_too_much_workload Job).
Proof.
  unfold src_busy_interval_too_much_workload, tgt_busy_interval_too_much_workload.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tbR tbL Htb.
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_imp; first exact ((BPc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ (clb_succ_rel _ _ Htb))).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ Ht1 Ht) (ct_decide_le _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht1 Hdl)))).
    exact (NQc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  exact (sub_nat_lt_correspondence _ _ _ _ (clb_service_of_hep_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j _ _ Ht1 _ _ (sub_add_correspondence _ _ _ _ Ht1 Hdl)) (clb_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j)).
Qed.

Definition src_busy_interval_workload_larger_than_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.busy_interval_workload_larger_than_interval Job)).
Definition tgt_busy_interval_workload_larger_than_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_workload_larger_than_interval Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_busy_interval_workload_larger_than_interval_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_workload_larger_than_interval Job) (tgt_busy_interval_workload_larger_than_interval Job).
Proof.
  unfold src_busy_interval_workload_larger_than_interval, tgt_busy_interval_workload_larger_than_interval.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_forall_nat => tbR tbL Htb.
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_imp; first exact ((BPc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ (clb_succ_rel _ _ Htb))).
  apply: ct_forall_nat => pbR pbL Hpb.
  apply: ct_imp; first exact (PIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Hpb).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ Ht1 Ht) (ct_decide_le _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht1 Hdl)))).
    exact (NQc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  exact (sub_nat_lt_correspondence _ _ _ _ Hdl (sub_add_correspondence _ _ _ _ Hpb (clb_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j))).
Qed.

Definition src_busy_interval_is_bounded (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.busy_interval_is_bounded Job)).
Definition tgt_busy_interval_is_bounded (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_is_bounded Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_busy_interval_is_bounded_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_is_bounded Job) (tgt_busy_interval_is_bounded Job).
Proof.
  unfold src_busy_interval_is_bounded, tgt_busy_interval_is_bounded.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_forall_nat => tbR tbL Htb.
  apply: ct_forall_nat => t1R t1L Ht1.
  apply: ct_imp; first exact ((BPc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ (clb_succ_rel _ _ Htb))).
  apply: ct_forall_nat => pbR pbL Hpb.
  apply: ct_imp; first exact (PIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Hpb).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Hpb (clb_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j)) Hdl).
  apply: ct_exists_nat => t2R t2L Ht2.
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ Ht2 (sub_add_correspondence _ _ _ _ Ht1 Hdl)).
  exact (BIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ Ht2).
Qed.

Definition src_exists_busy_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.exists_busy_interval Job)).
Definition tgt_exists_busy_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_exists_busy_interval Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_exists_busy_interval_correspondence (Job : eqType) :
  PropSPropRel (src_exists_busy_interval Job) (tgt_exists_busy_interval Job).
Proof.
  unfold src_exists_busy_interval, tgt_exists_busy_interval.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_imp; first exact (clb_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => pbR pbL Hpb.
  apply: ct_imp; first exact (PIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Hpb).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp.
  { apply: ct_forall_nat => t1R t1L Ht1.
    exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Hpb (clb_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j)) Hdl). }
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_exists_nat => t1R t1L Ht1. apply: ct_exists_nat => t2R t2L Ht2.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ht1 (Hja j)) (ct_decide_lt _ _ _ _ (Hja j) Ht2))).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ Ht2 (sub_add_correspondence _ _ _ _ Ht1 Hdl)).
  exact (BIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ Ht2).
Qed.

Definition src_busy_interval_bounds_response_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.busy_interval_bounds_response_time Job)).
Definition tgt_busy_interval_bounds_response_time (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_bounds_response_time Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_busy_interval_bounds_response_time_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_bounds_response_time Job) (tgt_busy_interval_bounds_response_time Job).
Proof.
  unfold src_busy_interval_bounds_response_time, tgt_busy_interval_bounds_response_time.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_imp; first exact (clb_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => pbR pbL Hpb.
  apply: ct_imp; first exact (PIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Hpb).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp.
  { apply: ct_forall_nat => t1R t1L Ht1.
    exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Hpb (clb_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht1 Hdl)) hR hL Hh j)) Hdl). }
  exact (ct_bool_truth _ _ (clb_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Hja j) Hdl))).
Qed.

Definition src_no_carry_in_implies_quiet_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.no_carry_in_implies_quiet_time Job)).
Definition tgt_no_carry_in_implies_quiet_time (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_no_carry_in_implies_quiet_time Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_no_carry_in_implies_quiet_time_correspondence (Job : eqType) :
  PropSPropRel (src_no_carry_in_implies_quiet_time Job) (tgt_no_carry_in_implies_quiet_time Job).
Proof.
  unfold src_no_carry_in_implies_quiet_time, tgt_no_carry_in_implies_quiet_time.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs tR tL Ht).
  exact (QTc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht).
Qed.

Definition src_idle_instant_implies_no_carry_in_at_t (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t Job)).
Definition tgt_idle_instant_implies_no_carry_in_at_t (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_idle_instant_implies_no_carry_in_at_t Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_idle_instant_implies_no_carry_in_at_t_correspondence (Job : eqType) :
  PropSPropRel (src_idle_instant_implies_no_carry_in_at_t Job) (tgt_idle_instant_implies_no_carry_in_at_t Job).
Proof.
  unfold src_idle_instant_implies_no_carry_in_at_t, tgt_idle_instant_implies_no_carry_in_at_t.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_US_is_idle Job sR sL Hs tR tL Ht)).
  exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs tR tL Ht).
Qed.

Definition src_idle_instant_implies_no_carry_in_at_t_pl_1 (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t_pl_1 Job)).
Definition tgt_idle_instant_implies_no_carry_in_at_t_pl_1 (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_idle_instant_implies_no_carry_in_at_t_pl_1 Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_idle_instant_implies_no_carry_in_at_t_pl_1_correspondence (Job : eqType) :
  PropSPropRel (src_idle_instant_implies_no_carry_in_at_t_pl_1 Job) (tgt_idle_instant_implies_no_carry_in_at_t_pl_1 Job).
Proof.
  unfold src_idle_instant_implies_no_carry_in_at_t_pl_1, tgt_idle_instant_implies_no_carry_in_at_t_pl_1.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_US_is_idle Job sR sL Hs tR tL Ht)).
  exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs _ _ (clb_succ_rel _ _ Ht)).
Qed.

Definition src_no_carry_in_at_the_beginning (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.no_carry_in_at_the_beginning Job)).
Definition tgt_no_carry_in_at_the_beginning (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_no_carry_in_at_the_beginning Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_no_carry_in_at_the_beginning_correspondence (Job : eqType) :
  PropSPropRel (src_no_carry_in_at_the_beginning Job) (tgt_no_carry_in_at_the_beginning Job).
Proof.
  unfold src_no_carry_in_at_the_beginning, tgt_no_carry_in_at_the_beginning.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: (clb_forall_sched Job) => sR sL Hs.
  exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs _ _ (sub_nat_rel_canonical 0)).
Qed.

Definition src_total_service_is_bounded_by_Δ (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.total_service_is_bounded_by_Δ Job)).
Definition tgt_total_service_is_bounded_by_Δ (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_total_service_is_bounded_by__UU0394_ Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_total_service_is_bounded_by_Δ_correspondence (Job : eqType) :
  PropSPropRel (src_total_service_is_bounded_by_Δ Job) (tgt_total_service_is_bounded_by_Δ Job).
Proof.
  unfold src_total_service_is_bounded_by_Δ, tgt_total_service_is_bounded_by_Δ.
  apply: clb_forall_par => jaR jaL Hja.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (clb_service_of_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ (sub_nat_rel_canonical 0) (sub_add_correspondence _ _ _ _ Ht Hdl)) _ _ (fun _ => ct_bool_canonical true) _ _ Ht _ _ (sub_add_correspondence _ _ _ _ Ht Hdl)) Hdl).
Qed.

Definition src_low_total_service_implies_existence_of_time_with_no_carry_in (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.low_total_service_implies_existence_of_time_with_no_carry_in Job)).
Definition tgt_low_total_service_implies_existence_of_time_with_no_carry_in (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_low_total_service_implies_existence_of_time_with_no_carry_in Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_low_total_service_implies_existence_of_time_with_no_carry_in_correspondence (Job : eqType) :
  PropSPropRel (src_low_total_service_implies_existence_of_time_with_no_carry_in Job) (tgt_low_total_service_implies_existence_of_time_with_no_carry_in Job).
Proof.
  unfold src_low_total_service_implies_existence_of_time_with_no_carry_in, tgt_low_total_service_implies_existence_of_time_with_no_carry_in.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (clb_service_of_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ (sub_nat_rel_canonical 0) (sub_add_correspondence _ _ _ _ Ht Hdl)) _ _ (fun _ => ct_bool_canonical true) _ _ Ht _ _ (sub_add_correspondence _ _ _ _ Ht Hdl)) Hdl).
  apply: ct_exists_nat => dR dL Hd.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hd Hdl).
  exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs _ _ (sub_add_correspondence _ _ _ _ (clb_succ_rel _ _ Ht) Hd)).
Qed.

Definition src_completion_of_all_jobs_implies_no_carry_in (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.completion_of_all_jobs_implies_no_carry_in Job)).
Definition tgt_completion_of_all_jobs_implies_no_carry_in (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_completion_of_all_jobs_implies_no_carry_in Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_completion_of_all_jobs_implies_no_carry_in_correspondence (Job : eqType) :
  PropSPropRel (src_completion_of_all_jobs_implies_no_carry_in Job) (tgt_completion_of_all_jobs_implies_no_carry_in Job).
Proof.
  unfold src_completion_of_all_jobs_implies_no_carry_in, tgt_completion_of_all_jobs_implies_no_carry_in.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _ (clb_WL_workload_of_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hdl)) _ _ (fun _ => ct_bool_canonical true)) Hdl). }
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs tR tL Ht).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (clb_service_of_jobs Job sR sL Hs _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ (sub_nat_rel_canonical 0) (sub_add_correspondence _ _ _ _ Ht Hdl)) _ _ (fun _ => ct_bool_canonical true) _ _ Ht _ _ (sub_add_correspondence _ _ _ _ Ht Hdl)) Hdl).
  exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs _ _ (sub_add_correspondence _ _ _ _ Ht Hdl)).
Qed.

Definition src_processor_is_not_too_busy (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.processor_is_not_too_busy Job)).
Definition tgt_processor_is_not_too_busy (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_processor_is_not_too_busy Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_processor_is_not_too_busy_correspondence (Job : eqType) :
  PropSPropRel (src_processor_is_not_too_busy Job) (tgt_processor_is_not_too_busy Job).
Proof.
  unfold src_processor_is_not_too_busy, tgt_processor_is_not_too_busy.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _ (clb_WL_workload_of_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hdl)) _ _ (fun _ => ct_bool_canonical true)) Hdl). }
  apply: ct_forall_nat => tR tL Ht. apply: ct_exists_nat => dR dL Hd.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hd Hdl).
  exact (NCc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs _ _ (sub_add_correspondence _ _ _ _ Ht Hd)).
Qed.

Definition src_exists_busy_interval_from_total_workload_bound (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyIntervalJLFP.exists_busy_interval_from_total_workload_bound Job)).
Definition tgt_exists_busy_interval_from_total_workload_bound (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_exists_busy_interval_from_total_workload_bound Job (ct_decidable_eq Job))).
Theorem BusyIntervalJLFP_exists_busy_interval_from_total_workload_bound_correspondence (Job : eqType) :
  PropSPropRel (src_exists_busy_interval_from_total_workload_bound Job) (tgt_exists_busy_interval_from_total_workload_bound Job).
Proof.
  unfold src_exists_busy_interval_from_total_workload_bound, tgt_exists_busy_interval_from_total_workload_bound.
  apply: clb_forall_par => jaR jaL Hja. apply: clb_forall_par => cR cL Hc.
  apply: (clb_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (clb_consistent Job jaR jaL Hja aR aL Ha).
  apply: (clb_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (clb_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (clb_forall_rel Job) => hR hL Hh.
  apply: ct_imp; first exact (clb_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (clb_LP_work_conserving Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs).
  apply: ct_imp; first exact (clb_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (clb_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (clb_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => dlR dlL Hdl.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdl).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _ (clb_WL_workload_of_jobs Job cR cL Hc _ _ (clb_jobs_arrived_between Job aR aL Ha _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hdl)) _ _ (fun _ => ct_bool_canonical true)) Hdl). }
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clb_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clb_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_exists_nat => t1R t1L Ht1. apply: ct_exists_nat => t2R t2L Ht2.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ht1 (Hja j)) (ct_decide_lt _ _ _ _ (Hja j) Ht2))).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ Ht2 (sub_add_correspondence _ _ _ _ Ht1 Hdl)).
  exact (BIc Job jaR jaL cR cL Hja Hc aR aL Ha sR sL Hs hR hL Hh j _ _ Ht1 _ _ Ht2).
Qed.
