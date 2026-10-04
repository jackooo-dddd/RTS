From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.list util.nondecreasing util.epsilon classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task classic.model.schedule.uni.schedule classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.platform.limited.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicLimitedModel.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicLimitedModelBase ClassicLimitedModelList ClassicLimitedModelList1.



Module I := ImportedClassicLimitedModel.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/platform/limited.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job/task parameters
    pointwise through [SubNatRel]; preemption models [Job -> time -> bool] pointwise on related times and Booleans;
    uniprocessor schedules pointwise through the option map; arrival sequences pointwise on related times; priority
    policies pointwise on Booleans; all with two-way totals. Preemption-point lists [seq nat] are related to
    Lean [List Nat] (universe instance [List_inst1]) elementwise through the Nat embedding ([ClListRel1
    sub_nat_to_imported], [ClassicLimitedModelList1]); task sets [seq Task] by [ClListRel cid]; the v0.6 utility
    functions [distances], [max0], [first0], [last0] and [nondecreasing_sequence] are related by structural
    induction against the imported accepted v0.6 Lean definitions (by computation of the imported recursors);
    [x \in s] for Nat lists through [cl1_mem_rel_list] and the Lean [decide] by [ct_decide_bool]; [nth 0 s n] is
    [getD]; the uniprocessor service (a [Finset.Ico] sum) through the projection fixture as in the accepted
    platform-definitions certificate. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma clm_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma clm_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma clm_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) clm_false_rel). Qed.

Lemma clm_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma clm_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma clm_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma clm_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma clm_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (clm_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => clm_unmap_rel T l) PR PL).
Qed.

Definition ClmParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma clm_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, ClmParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (clm_forall_cover _ _ (ClmParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint clm_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (clm_natl s') end.

Definition clm_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma clm_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) clm_one) (clm_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) clm_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (clm_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma clm_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma clm_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma clm_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma clm_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH clm_cl_append. reflexivity.
Qed.

Lemma clm_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition ClmFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition ClmArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition clm_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition clm_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma clm_arr_canonical aR : ClmArrRel aR (clm_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /clm_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma clm_arr_surjective aL : ClmArrRel (clm_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma clm_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, ClmArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (clm_forall_cover _ _ ClmArrRel clm_arr_to_target clm_arr_to_source clm_arr_canonical clm_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma clm_arrives_in aR aL (Ha : ClmArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (clm_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

Fixpoint clm_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (clm_snatl s') end.

Lemma clm_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (clm_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (clm_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma clm_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (clm_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (clm_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma clm_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition ClmFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma clm_fun_canonical FR FL (HF : ClmFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma clm_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma clm_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : ClmFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := clm_nat_sub_canonical nR mR.
  rewrite clm_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (clm_foldr_add FL FR (clm_fun_canonical FR FL HF)).
  by rewrite clm_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition clm_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition clm_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma clm_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma clm_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (clm_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition ClmSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition clm_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition clm_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma clm_sched_canonical sR : ClmSchedRel sR (clm_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /clm_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma clm_sched_surjective sL : ClmSchedRel (clm_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /clm_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma clm_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, ClmSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (clm_forall_cover _ _ ClmSchedRel clm_sched_to_target clm_sched_to_source clm_sched_canonical clm_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma clm_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, ClmSchedRel Job sR (clm_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), ClmSchedRel Job (clm_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (clm_sched_canonical Job) (clm_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClmSchedRel Job sR sL.

Lemma clm_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (clm_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (clm_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma clm_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (clm_US_scheduled_at j tR tL Ht)). Qed.

Lemma clm_service_at_fun j : ClmFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (clm_US_service_at j kR kL Hk). Qed.

Lemma clm_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (clm_ico _ _ _ _ _ _ H1 H2 (clm_service_at_fun j)). Qed.

Lemma clm_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (clm_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

End USchedDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClmSchedRel Job sR sL.

End UplatDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition ClmRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma clm_rel_canonical (T : Type) (rR : T -> T -> bool) : ClmRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma clm_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : ClmRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma clm_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, ClmRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (clm_forall_cover _ _ (ClmRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (clm_rel_canonical T) (clm_rel_surjective T) PR PL).
Qed.

Definition ClmJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClmRelRel T (rR tR) (rL tL).

Lemma clm_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  ClmJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma clm_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  ClmJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma clm_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, ClmJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (clm_forall_cover _ _ (ClmJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (clm_jldp_canonical T) (clm_jldp_surjective T) PR PL).
Qed.

Lemma clm_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma clm_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section LPDPmRel.
Variable Job : eqType.
Definition ClmPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma clm_pm_canonical pR : ClmPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma clm_pm_surjective pL : ClmPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma clm_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, ClmPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (clm_forall_cover _ _ ClmPmRel _ _ clm_pm_canonical clm_pm_surjective PR PL). Qed.

End LPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClmSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : ClmPmRel Job pR pL.

Notation SA := (clm_US_scheduled_at Job sR sL Hs).
Notation SV := (clm_US_service Job sR sL Hs).

Lemma clm_LPD_not_preemptive_implies_scheduled j :
  PropSPropRel (LimitedPreemptionPlatform.not_preemptive_implies_scheduled sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_not_preemptive_implies_scheduled Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hp j _ _ (SV j tR tL Ht)))).
  exact (ct_bool_truth _ _ (SA j tR tL Ht)).
Qed.

Lemma clm_LPD_execution_starts_with_preemption_point j :
  PropSPropRel (LimitedPreemptionPlatform.execution_starts_with_preemption_point sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_execution_starts_with_preemption_point Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  have Ht1 := clm_succ_rel _ _ Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (SA j tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j _ _ Ht1)).
  exact (ct_bool_truth _ _ (Hp j _ _ (SV j _ _ Ht1))).
Qed.

Lemma clm_LPD_correct_preemption_model arrR arrL (Harr : ClmArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.correct_preemption_model arrR sR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_correct_preemption_model Job dJ arrL sL pL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clm_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (clm_LPD_not_preemptive_implies_scheduled j).
  exact (clm_LPD_execution_starts_with_preemption_point j).
Qed.

End LPDDefs.

Section LPDDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : ClmPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : ClmParRel Job cR cL) (Hm : ClmParRel Job mR mL) (Htm : ClmParRel Task tmR tmL).

Lemma clm_LPD_job_cannot_become_nonpreemptive_before_execution j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution Job dJ pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (sub_nat_rel_canonical 0))). Qed.

Lemma clm_LPD_job_cannot_be_nonpreemptive_after_completion j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion cR pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion Job dJ cL pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (Hc j))). Qed.

Lemma clm_LPD_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (job_task : Job -> Task)
    arrR arrL (Harr : ClmArrRel Job arrR arrL) j :
  PropSPropRel (LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR mR tmR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment Task dT Job dJ job_task arrL mL tmL j).
Proof.
  apply: ct_imp; first exact (clm_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_le_correspondence _ _ _ _ (Hm j) (Htm (job_task j))).
Qed.

Lemma clm_LPD_nonpreemptive_regions_have_bounded_length j :
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

Lemma clm_LPD_model_with_bounded_nonpreemptive_segments (job_task : Job -> Task)
    arrR arrL (Harr : ClmArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments cR job_task arrR pR mR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments Task dT Job dJ cL job_task arrL pL mL tmL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clm_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (clm_LPD_job_cannot_become_nonpreemptive_before_execution j).
  apply: ct_and; first exact (clm_LPD_job_cannot_be_nonpreemptive_after_completion j).
  apply: ct_and; first exact (clm_LPD_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR arrL Harr j).
  exact (clm_LPD_nonpreemptive_regions_have_bounded_length j).
Qed.

End LPDDefs2.

Section LPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClmSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : ClmParRel Job aR aL) (Hc : ClmParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : ClmArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : ClmPmRel Job pR pL.

End LPDResp.

(* ------------------------------------------------------------------ *)
(** * Nat lists (universe instance [List_inst1]) through the Nat embedding *)

Notation NL := (I.List_inst1 Lean.Nat).
Notation nc := sub_nat_to_imported.
Definition ClmNlRel (sR : seq nat) (sL : NL) : SProp := ClListRel1 sub_nat_to_imported sR sL.

Lemma clm_dc x : Logic.eq (sub_nat_to_rocq (sub_nat_to_imported x)) x.
Proof. exact (sub_nat_rocq_roundtrip x). Qed.
Lemma clm_cd y : Logic.eq (sub_nat_to_imported (sub_nat_to_rocq y)) y.
Proof. exact (imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip y)). Qed.

Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma clm_distances_eq : forall s,
  Logic.eq (cl1_map nc (prosa.util.nondecreasing.distances s)) (I.Prosa_Util_Nondecreasing_distances (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicLimitedModelInterface_distances_nil)).
  case: s IH => [|y ys] IH; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_distances_single (nc x)))).
  rewrite (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_distances_cons2 (nc x) (nc y) (cl1_map nc ys))).
  have Hs : Logic.eq (prosa.util.nondecreasing.distances [:: x, y & ys]) ((y - x) :: prosa.util.nondecreasing.distances (y :: ys)) by rewrite /prosa.util.nondecreasing.distances /= drop0.
  rewrite Hs.
  change (Logic.eq (I.List_cons_inst1 Lean.Nat (nc (y - x)) (cl1_map nc (prosa.util.nondecreasing.distances (y :: ys))))
    (I.List_cons_inst1 Lean.Nat (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) (nc y) (nc x))
       (I.Prosa_Util_Nondecreasing_distances (cl1_map nc (y :: ys))))).
  rewrite -IH. exact (f_equal (fun z => I.List_cons_inst1 Lean.Nat z (cl1_map nc (prosa.util.nondecreasing.distances (y :: ys))))
    (EQ (ct_sub_rel _ _ _ _ (sub_nat_rel_canonical y) (sub_nat_rel_canonical x)))).
Qed.

Lemma clm_distances sR sL : ClmNlRel sR sL -> ClmNlRel (prosa.util.nondecreasing.distances sR) (I.Prosa_Util_Nondecreasing_distances sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (clm_distances_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_Nondecreasing_distances _ _ H)).
Qed.

Lemma clm_foldl_max_eq : forall s z,
  Logic.eq (nc (seq.foldl maxn z s)) (I.List_foldl_inst3 Lean.Nat Lean.Nat I.Nat_max (nc z) (cl1_map nc s)).
Proof.
  elim => [|x s IH] z; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_foldl_max_nil (nc z)))).
  rewrite (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_foldl_max_cons (nc z) (nc x) (cl1_map nc s))).
  rewrite -(EQ (ct_max_rel _ _ _ _ (sub_nat_rel_canonical z) (sub_nat_rel_canonical x))).
  exact (IH (maxn z x)).
Qed.

Lemma clm_max0 sR sL : ClmNlRel sR sL -> SubNatRel (prosa.util.list.max0 sR) (I.Prosa_Util_List_max0 sL).
Proof.
  intro H.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicLimitedModelInterface_max0_eq sL))).
  exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (clm_foldl_max_eq sR 0))
    (sub_imported_eq_congr (fun l => I.List_foldl_inst3 Lean.Nat Lean.Nat I.Nat_max (nc 0) l) _ _ H)).
Qed.

Lemma clm_first0_eq s : Logic.eq (nc (prosa.util.list.first0 s)) (I.Prosa_Util_List_first0 (cl1_map nc s)).
Proof.
  case: s => [|x s]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicLimitedModelInterface_first0_nil)).
  exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_first0_cons (nc x) (cl1_map nc s)))).
Qed.

Lemma clm_first0 sR sL : ClmNlRel sR sL -> SubNatRel (prosa.util.list.first0 sR) (I.Prosa_Util_List_first0 sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (clm_first0_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_List_first0 _ _ H)).
Qed.

Lemma clm_last0_eq : forall s, Logic.eq (nc (prosa.util.list.last0 s)) (I.Prosa_Util_List_last0 (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicLimitedModelInterface_last0_nil)).
  case: s IH => [|y ys] IH; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_last0_single (nc x)))).
  rewrite (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_last0_cons2 (nc x) (nc y) (cl1_map nc ys))).
  exact IH.
Qed.

Lemma clm_last0 sR sL : ClmNlRel sR sL -> SubNatRel (prosa.util.list.last0 sR) (I.Prosa_Util_List_last0 sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (clm_last0_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_List_last0 _ _ H)).
Qed.

Lemma clm_nth_eq : forall s n,
  Logic.eq (nc (seq.nth 0 s n)) (I.List_getD_inst1 Lean.Nat (cl1_map nc s) (nc n) (nc 0)).
Proof.
  elim => [|x s IH] n; first by case: n => [|n]; exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_getD_nil _ (nc 0)))).
  case: n => [|n]; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_getD_cons_zero (nc x) (cl1_map nc s) (nc 0)))).
  exact (Logic.eq_trans (IH n) (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_getD_cons_succ (nc x) (cl1_map nc s) (nc n) (nc 0))))).
Qed.

Lemma clm_nth sR sL (H : ClmNlRel sR sL) nR nL (Hn : SubNatRel nR nL) :
  SubNatRel (seq.nth 0 sR nR) (I.List_getD_inst1 Lean.Nat sL nL (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))).
Proof.
  exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (clm_nth_eq sR nR))
    (sub_imported_eq_congr2 (fun l m => I.List_getD_inst1 Lean.Nat l m (nc 0)) _ _ _ _ H Hn)).
Qed.

Lemma clm_size_eq : forall s, Logic.eq (nc (seq.size s)) (I.List_length_inst1 Lean.Nat (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicLimitedModelInterface_length_nil)).
  rewrite (EQ (I.Prosa_Validation_ClassicLimitedModelInterface_length_cons (nc x) (cl1_map nc s))) -IH. reflexivity.
Qed.

Lemma clm_size sR sL : ClmNlRel sR sL -> SubNatRel (seq.size sR) (I.List_length_inst1 Lean.Nat sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (clm_size_eq sR))
    (sub_imported_eq_congr (I.List_length_inst1 Lean.Nat) _ _ H)).
Qed.

Lemma clm_nmem xR xL (Hx : SubNatRel xR xL) sR sL (H : ClmNlRel sR sL) :
  PropSPropRel (xR \in sR)
    (I.Membership_mem_inst3 Lean.Nat NL (I.List_instMembership_inst1 Lean.Nat) sL xL).
Proof.
  rewrite (cl_nat_logic _ _ Hx).
  exact (cl1_mem_rel_list _ Lean.Nat sub_nat_to_imported sub_nat_to_rocq clm_dc xR sR sL H).
Qed.

Lemma clm_nl_eq sR sL tR tL (Hs : ClmNlRel sR sL) (Ht : ClmNlRel tR tL) :
  PropSPropRel (Logic.eq sR tR) (Lean.eq sL tL).
Proof.
  rewrite (cl1_list_logic _ _ _ Hs) (cl1_list_logic _ _ _ Ht). clear Hs Ht.
  apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E.
    by rewrite -(cl1_unmap_map nc sub_nat_to_rocq clm_dc sR) -(cl1_unmap_map nc sub_nat_to_rocq clm_dc tR) E'.
Qed.

Lemma clm_andb_and a b (PA PB : SProp) :
  PropSPropRel (is_true a) PA -> PropSPropRel (is_true b) PB -> PropSPropRel (is_true (a && b)) (And PA PB).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - move=> E. exact (And_intro PA PB (prop_to_sprop _ _ Ha (proj1 (elimT andP E))) (prop_to_sprop _ _ Hb (proj2 (elimT andP E)))).
  - intros [x y]. apply strictly_inhabits. apply/andP. split; [exact (sprop_to_prop _ _ Ha x) | exact (sprop_to_prop _ _ Hb y)].
Qed.

Lemma clm_nondecreasing sR sL (H : ClmNlRel sR sL) :
  PropSPropRel (prosa.util.nondecreasing.nondecreasing_sequence sR) (I.Prosa_Util_Nondecreasing_nondecreasing_sequence sL).
Proof.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicLimitedModelInterface_nondecreasing_sequence_eq sL)).
  apply: ct_forall_nat => n1R n1L H1. apply: ct_forall_nat => n2R n2L H2.
  apply: ct_imp.
  - exact (clm_andb_and _ _ _ _ (sub_nat_le_correspondence _ _ _ _ H1 H2) (sub_nat_lt_correspondence _ _ _ _ H2 (clm_size _ _ H))).
  - exact (sub_nat_le_correspondence _ _ _ _ (clm_nth _ _ H _ _ H1) (clm_nth _ _ H _ _ H2)).
Qed.

Definition ClmPpRel (T : Type) (pR : T -> seq nat) (pL : T -> NL) : SProp := forall x, ClmNlRel (pR x) (pL x).

Lemma clm_forall_pp (T : Type) (PR : (T -> seq nat) -> Prop) (PL : (T -> NL) -> SProp) :
  (forall pR pL, ClmPpRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (clm_forall_cover _ _ (ClmPpRel T) (fun pR x => cl1_map nc (pR x)) (fun pL x => cl1_unmap sub_nat_to_rocq (pL x))
    (fun pR x => @Lean.eq_refl _ _)
    (fun pL x => coq_eq_to_imported_eq _ _ (cl1_map_unmap nc sub_nat_to_rocq clm_cd (pL x))) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JobDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> seq nat) (pL : Job -> NL).
Hypothesis Hp : ClmPpRel Job pR pL.

Theorem ModelWithLimitedPreemptions_lengths_of_segments_correspondence j :
  ClmNlRel (@ModelWithLimitedPreemptions.lengths_of_segments Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_lengths_of_segments Job dJ pL j).
Proof. exact (clm_distances _ _ (Hp j)). Qed.

Theorem ModelWithLimitedPreemptions_job_max_nps_correspondence j :
  SubNatRel (@ModelWithLimitedPreemptions.job_max_nps Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_max_nps Job dJ pL j).
Proof. exact (clm_max0 _ _ (ModelWithLimitedPreemptions_lengths_of_segments_correspondence j)). Qed.

Theorem ModelWithLimitedPreemptions_job_last_nps_correspondence j :
  SubNatRel (@ModelWithLimitedPreemptions.job_last_nps Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_last_nps Job dJ pL j).
Proof. exact (clm_last0 _ _ (ModelWithLimitedPreemptions_lengths_of_segments_correspondence j)). Qed.

Theorem ModelWithLimitedPreemptions_can_be_preempted_for_model_with_limited_preemptions_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions Job pR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_can_be_preempted_for_model_with_limited_preemptions Job dJ pL j tL).
Proof. exact (ct_decide_bool _ _ _ (clm_nmem _ _ Ht _ _ (Hp j))). Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : ClmParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : ClmArrRel Job arrR arrL.
Notation ARR := (clm_arrives_in Job arrR arrL Harr).

Theorem ModelWithLimitedPreemptions_job_with_zero_cost_consists_of_one_empty_segment_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.job_with_zero_cost_consists_of_one_empty_segment Job cR arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_with_zero_cost_consists_of_one_empty_segment Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (Hc j) (sub_nat_rel_canonical 0)).
  exact (clm_nl_eq _ _ _ _ (Hp j) (@Lean.eq_refl _ (cl1_map nc [:: 0; 0]))).
Qed.

Theorem ModelWithLimitedPreemptions_last_segment_is_positive_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.last_segment_is_positive Job cR arrR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_last_segment_is_positive Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (ModelWithLimitedPreemptions_job_last_nps_correspondence j)).
Qed.

Theorem ModelWithLimitedPreemptions_beginning_of_execution_in_preemption_points_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.beginning_of_execution_in_preemption_points Job arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_beginning_of_execution_in_preemption_points Job dJ arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (clm_first0 _ _ (Hp j)) (sub_nat_rel_canonical 0)).
Qed.

Theorem ModelWithLimitedPreemptions_end_of_execution_in_preemption_points_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.end_of_execution_in_preemption_points Job cR arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_end_of_execution_in_preemption_points Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (clm_last0 _ _ (Hp j)) (Hc j)).
Qed.

Theorem ModelWithLimitedPreemptions_preemption_points_is_nondecreasing_sequence_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.preemption_points_is_nondecreasing_sequence Job arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_preemption_points_is_nondecreasing_sequence Job dJ arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (clm_nondecreasing _ _ (Hp j)).
Qed.

Theorem ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.limited_preemptions_job_model Job cR arrR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_limited_preemptions_job_model Job dJ cL arrL pL).
Proof.
  apply: ct_and; first exact ModelWithLimitedPreemptions_job_with_zero_cost_consists_of_one_empty_segment_correspondence.
  apply: ct_and; first exact ModelWithLimitedPreemptions_last_segment_is_positive_correspondence.
  apply: ct_and; first exact ModelWithLimitedPreemptions_beginning_of_execution_in_preemption_points_correspondence.
  apply: ct_and; first exact ModelWithLimitedPreemptions_end_of_execution_in_preemption_points_correspondence.
  exact ModelWithLimitedPreemptions_preemption_points_is_nondecreasing_sequence_correspondence.
Qed.

Theorem ModelWithLimitedPreemptions_is_schedule_with_limited_preemptions_correspondence sR sL (Hs : ClmSchedRel Job sR sL) :
  PropSPropRel (@ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions Job arrR pR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_is_schedule_with_limited_preemptions Job dJ arrL pL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _
    (ModelWithLimitedPreemptions_can_be_preempted_for_model_with_limited_preemptions_correspondence j _ _ (clm_US_service Job sR sL Hs j tR tL Ht)))).
  exact (ct_bool_truth _ _ (clm_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

End JobDefs.

Section TaskDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tpR : Task -> seq nat) (tpL : Task -> NL).
Hypothesis Htp : ClmPpRel Task tpR tpL.

Theorem ModelWithLimitedPreemptions_task_last_nps_correspondence tsk :
  SubNatRel (@ModelWithLimitedPreemptions.task_last_nps Task tpR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_last_nps Task dT tpL tsk).
Proof. exact (clm_last0 _ _ (clm_distances _ _ (Htp tsk))). Qed.

Theorem ModelWithLimitedPreemptions_task_max_nps_correspondence tsk :
  SubNatRel (@ModelWithLimitedPreemptions.task_max_nps Task tpR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_max_nps Task dT tpL tsk).
Proof. exact (clm_max0 _ _ (clm_distances _ _ (Htp tsk))). Qed.

Variables (tsR : seq Task) (tsL : I.List Task).
Hypothesis Hts : ClListRel cid tsR tsL.
Notation MEM := (fun tsk => clm_mem Task tsk tsR tsL Hts).

Theorem ModelWithLimitedPreemptions_task_beginning_of_execution_in_preemption_points_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.task_beginning_of_execution_in_preemption_points Task tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_beginning_of_execution_in_preemption_points Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (sub_nat_eq_correspondence _ _ _ _ (clm_first0 _ _ (Htp tsk)) (sub_nat_rel_canonical 0)).
Qed.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : ClmParRel Task tcR tcL.

Theorem ModelWithLimitedPreemptions_task_end_of_execution_in_preemption_points_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.task_end_of_execution_in_preemption_points Task tcR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_end_of_execution_in_preemption_points Task dT tcL tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (sub_nat_eq_correspondence _ _ _ _ (clm_last0 _ _ (Htp tsk)) (Htc tsk)).
Qed.

Theorem ModelWithLimitedPreemptions_task_preemption_points_is_nondecreasing_sequence_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.task_preemption_points_is_nondecreasing_sequence Task tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_preemption_points_is_nondecreasing_sequence Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (clm_nondecreasing _ _ (Htp tsk)).
Qed.

Theorem ModelWithLimitedPreemptions_task_segments_are_nonempty_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.task_segments_are_nonempty Task tpR tsR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_segments_are_nonempty Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => nR nL Hn.
  apply: ct_imp; first exact (MEM tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hn (clm_size _ _ (clm_distances _ _ (Htp tsk)))).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (clm_nth _ _ (clm_distances _ _ (Htp tsk)) _ _ Hn)).
Qed.

End TaskDefs.

Section JobTaskDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variable job_task : Job -> Task.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : ClmArrRel Job arrR arrL.
Notation ARR := (clm_arrives_in Job arrR arrL Harr).
Variables (pR : Job -> seq nat) (pL : Job -> NL).
Hypothesis Hp : ClmPpRel Job pR pL.
Variables (tpR : Task -> seq nat) (tpL : Task -> NL).
Hypothesis Htp : ClmPpRel Task tpR tpL.

Theorem ModelWithLimitedPreemptions_job_consists_of_the_same_number_of_segments_as_task_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.job_consists_of_the_same_number_of_segments_as_task Task Job job_task arrR pR tpR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_consists_of_the_same_number_of_segments_as_task Task dT Job dJ job_task arrL pL tpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (clm_size _ _ (Hp j)) (clm_size _ _ (Htp (job_task j)))).
Qed.

Theorem ModelWithLimitedPreemptions_lengths_of_task_segments_bound_length_of_job_segments_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.lengths_of_task_segments_bound_length_of_job_segments Task Job job_task arrR pR tpR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_lengths_of_task_segments_bound_length_of_job_segments Task dT Job dJ job_task arrL pL tpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => nR nL Hn.
  apply: ct_imp; first exact (ARR j).
  exact (sub_nat_le_correspondence _ _ _ _ (clm_nth _ _ (clm_distances _ _ (Hp j)) _ _ Hn)
    (clm_nth _ _ (clm_distances _ _ (Htp (job_task j))) _ _ Hn)).
Qed.

Variables (tsR : seq Task) (tsL : I.List Task).
Hypothesis Hts : ClListRel cid tsR tsL.
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : ClmParRel Task tcR tcL.

Theorem ModelWithLimitedPreemptions_fixed_preemption_points_task_model_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.fixed_preemption_points_task_model Task tcR Job job_task arrR pR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_fixed_preemption_points_task_model Task dT tcL Job dJ job_task arrL pL tpL tsL).
Proof.
  apply: ct_and; first exact (ModelWithLimitedPreemptions_task_beginning_of_execution_in_preemption_points_correspondence Task tpR tpL Htp tsR tsL Hts).
  apply: ct_and; first exact (ModelWithLimitedPreemptions_task_end_of_execution_in_preemption_points_correspondence Task tpR tpL Htp tsR tsL Hts tcR tcL Htc).
  apply: ct_and; first exact (ModelWithLimitedPreemptions_task_preemption_points_is_nondecreasing_sequence_correspondence Task tpR tpL Htp tsR tsL Hts).
  apply: ct_and; first exact ModelWithLimitedPreemptions_job_consists_of_the_same_number_of_segments_as_task_correspondence.
  apply: ct_and; first exact ModelWithLimitedPreemptions_lengths_of_task_segments_bound_length_of_job_segments_correspondence.
  exact (ModelWithLimitedPreemptions_task_segments_are_nonempty_correspondence Task tpR tpL Htp tsR tsL Hts).
Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : ClmParRel Job cR cL.

Theorem ModelWithLimitedPreemptions_fixed_preemption_points_model_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.fixed_preemption_points_model Task tcR Job cR job_task arrR pR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_fixed_preemption_points_model Task dT tcL Job dJ cL job_task arrL pL tpL tsL).
Proof.
  apply: ct_and; first exact (ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence Job pR pL Hp cR cL Hc arrR arrL Harr).
  exact ModelWithLimitedPreemptions_fixed_preemption_points_task_model_correspondence.
Qed.

Variables (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypothesis Htm : ClmParRel Task tmR tmL.

Theorem ModelWithLimitedPreemptions_job_max_np_segment_le_task_max_np_segment_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.job_max_np_segment_le_task_max_np_segment Task Job job_task arrR pR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_max_np_segment_le_task_max_np_segment Task dT Job dJ job_task arrL pL tmL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_le_correspondence _ _ _ _ (ModelWithLimitedPreemptions_job_max_nps_correspondence Job pR pL Hp j) (Htm (job_task j))).
Qed.

Theorem ModelWithLimitedPreemptions_model_with_floating_nonpreemptive_regions_correspondence :
  PropSPropRel (@ModelWithLimitedPreemptions.model_with_floating_nonpreemptive_regions Task Job cR job_task arrR pR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_model_with_floating_nonpreemptive_regions Task dT Job dJ cL job_task arrL pL tmL).
Proof.
  apply: ct_and; first exact (ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence Job pR pL Hp cR cL Hc arrR arrL Harr).
  exact ModelWithLimitedPreemptions_job_max_np_segment_le_task_max_np_segment_correspondence.
Qed.

End JobTaskDefs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_list_of_preemption_point_is_not_empty (Job : eqType) : Prop :=
  ltac:(type_of_term (@ModelWithLimitedPreemptions.list_of_preemption_point_is_not_empty Job)).
Definition tgt_list_of_preemption_point_is_not_empty (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_list_of_preemption_point_is_not_empty Job (ct_decidable_eq Job))).
Theorem ModelWithLimitedPreemptions_list_of_preemption_point_is_not_empty_correspondence (Job : eqType) :
  PropSPropRel (src_list_of_preemption_point_is_not_empty Job) (tgt_list_of_preemption_point_is_not_empty Job).
Proof.
  unfold src_list_of_preemption_point_is_not_empty, tgt_list_of_preemption_point_is_not_empty.
  apply: (clm_forall_par Job) => cR cL Hc. apply: (clm_forall_arr Job) => arrR arrL Harr. apply: (clm_forall_pp Job) => pR pL Hp.
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence Job pR pL Hp cR cL Hc arrR arrL Harr).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (clm_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (clm_size _ _ (Hp j))).
Qed.

Definition src_zero_in_preemption_points (Job : eqType) : Prop :=
  ltac:(type_of_term (@ModelWithLimitedPreemptions.zero_in_preemption_points Job)).
Definition tgt_zero_in_preemption_points (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_zero_in_preemption_points Job (ct_decidable_eq Job))).
Theorem ModelWithLimitedPreemptions_zero_in_preemption_points_correspondence (Job : eqType) :
  PropSPropRel (src_zero_in_preemption_points Job) (tgt_zero_in_preemption_points Job).
Proof.
  unfold src_zero_in_preemption_points, tgt_zero_in_preemption_points.
  apply: (clm_forall_par Job) => cR cL Hc. apply: (clm_forall_arr Job) => arrR arrL Harr. apply: (clm_forall_pp Job) => pR pL Hp.
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence Job pR pL Hp cR cL Hc arrR arrL Harr).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (clm_arrives_in Job arrR arrL Harr j).
  exact (clm_nmem _ _ (sub_nat_rel_canonical 0) _ _ (Hp j)).
Qed.

Definition src_job_cost_in_nonpreemptive_points (Job : eqType) : Prop :=
  ltac:(type_of_term (@ModelWithLimitedPreemptions.job_cost_in_nonpreemptive_points Job)).
Definition tgt_job_cost_in_nonpreemptive_points (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_cost_in_nonpreemptive_points Job (ct_decidable_eq Job))).
Theorem ModelWithLimitedPreemptions_job_cost_in_nonpreemptive_points_correspondence (Job : eqType) :
  PropSPropRel (src_job_cost_in_nonpreemptive_points Job) (tgt_job_cost_in_nonpreemptive_points Job).
Proof.
  unfold src_job_cost_in_nonpreemptive_points, tgt_job_cost_in_nonpreemptive_points.
  apply: (clm_forall_par Job) => cR cL Hc. apply: (clm_forall_arr Job) => arrR arrL Harr. apply: (clm_forall_pp Job) => pR pL Hp.
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence Job pR pL Hp cR cL Hc arrR arrL Harr).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (clm_arrives_in Job arrR arrL Harr j).
  exact (clm_nmem _ _ (Hc j) _ _ (Hp j)).
Qed.

Definition src_number_of_preemption_points_at_least_two (Job : eqType) : Prop :=
  ltac:(type_of_term (@ModelWithLimitedPreemptions.number_of_preemption_points_at_least_two Job)).
Definition tgt_number_of_preemption_points_at_least_two (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_number_of_preemption_points_at_least_two Job (ct_decidable_eq Job))).
Theorem ModelWithLimitedPreemptions_number_of_preemption_points_at_least_two_correspondence (Job : eqType) :
  PropSPropRel (src_number_of_preemption_points_at_least_two Job) (tgt_number_of_preemption_points_at_least_two Job).
Proof.
  unfold src_number_of_preemption_points_at_least_two, tgt_number_of_preemption_points_at_least_two.
  apply: (clm_forall_par Job) => cR cL Hc. apply: (clm_forall_arr Job) => arrR arrL Harr. apply: (clm_forall_pp Job) => pR pL Hp.
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence Job pR pL Hp cR cL Hc arrR arrL Harr).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (clm_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 2) (clm_size _ _ (Hp j))).
Qed.

Definition src_model_with_fixed_preemption_points_is_correct (Job : eqType) : Prop :=
  ltac:(type_of_term (@ModelWithLimitedPreemptions.model_with_fixed_preemption_points_is_correct Job)).
Definition tgt_model_with_fixed_preemption_points_is_correct (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_model_with_fixed_preemption_points_is_correct Job (ct_decidable_eq Job))).
Theorem ModelWithLimitedPreemptions_model_with_fixed_preemption_points_is_correct_correspondence (Job : eqType) :
  PropSPropRel (src_model_with_fixed_preemption_points_is_correct Job) (tgt_model_with_fixed_preemption_points_is_correct Job).
Proof.
  unfold src_model_with_fixed_preemption_points_is_correct, tgt_model_with_fixed_preemption_points_is_correct.
  apply: (clm_forall_arr Job) => arrR arrL Harr. apply: (clm_forall_pp Job) => pR pL Hp. apply: (clm_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_is_schedule_with_limited_preemptions_correspondence Job pR pL Hp arrR arrL Harr sR sL Hs).
  exact (clm_LPD_correct_preemption_model Job sR sL Hs _ _ (ModelWithLimitedPreemptions_can_be_preempted_for_model_with_limited_preemptions_correspondence Job pR pL Hp) arrR arrL Harr).
Qed.

Definition src_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@ModelWithLimitedPreemptions.model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions Task Job)).
Definition tgt_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions (Task Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem ModelWithLimitedPreemptions_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions_correspondence (Task Job : eqType) :
  PropSPropRel (src_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions Task Job) (tgt_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions Task Job).
Proof.
  unfold src_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions, tgt_model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions.
  apply: (clm_forall_par Job) => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (clm_forall_arr Job) => arrR arrL Harr. apply: (clm_forall_pp Job) => pR pL Hp. apply: (clm_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_is_schedule_with_limited_preemptions_correspondence Job pR pL Hp arrR arrL Harr sR sL Hs).
  apply: (clm_forall_par Task) => tmR tmL Htm.
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_limited_preemptions_job_model_correspondence Job pR pL Hp cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ModelWithLimitedPreemptions_job_max_np_segment_le_task_max_np_segment_correspondence Task Job job_task arrR arrL Harr pR pL Hp tmR tmL Htm).
  exact (clm_LPD_model_with_bounded_nonpreemptive_segments Task Job _ _ (ModelWithLimitedPreemptions_can_be_preempted_for_model_with_limited_preemptions_correspondence Job pR pL Hp) cR cL _ _ tmR tmL Hc (ModelWithLimitedPreemptions_job_max_nps_correspondence Job pR pL Hp) Htm job_task arrR arrL Harr).
Qed.
