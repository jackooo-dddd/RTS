From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job
  classic.model.schedule.global.basic.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicScheduleBase ClassicScheduleList ClassicScheduleOrd.

Module I := ImportedClassicSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/global/basic/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean
    [DecidableEq] instances given by the eqTypes' decision procedures
    ([ct_decidable_eq]); [job_task] and jobs identified; natural numbers (times,
    [num_cpus]) by [SubNatRel]; processors ['I_n] and [Fin n] by their values
    ([CoOrdRel]); schedules pointwise on related processors and times, option
    values by the constructor map [cl_opt] ([CsSchedRel]); job parameters
    [Job -> time] pointwise through [SubNatRel]; sequences elementwise
    ([ClListRel]); arrival sequences pointwise on related times ([CsArrRel]); all
    with two-way totals.

    Computation.  [[exists cpu, P cpu]] against [(List.finRange n).any P]
    ([co_exists_rel], through the exported kernel-checked [finRange_any]);
    [\sum_(cpu < n | P cpu) 1] against the filtered [Fin] sum, rewritten by the
    exported kernel-checked [service_at_sum] into [∑ cpu, if P cpu then 1 else 0]
    and related by [co_sum_rel] (through [fin_sum_range']); [\cat_(cpu < n) F cpu]
    against [bigCatFin] ([co_bigcat_rel], through [bigCatFin_range']);
    [\cat_(t1 <= t < t2) F t] against [Prosa.Util.Notation.bigCat] (through
    [bigCat_range'], as in the accepted arrival_sequence certificate); [undup]
    against Mathlib's [List.dedup] (through the exported step equations
    [dedup_nil] / [dedup_cons_mem] / [dedup_cons_not_mem]); half-open
    [\sum_(m <= t < n) F t] against the projected Lean fold
    [List.foldr Nat.add 0 (List.map F (List.range' m (n - m) 1))] — the export
    form of [service] / [service_during] (definition-body projections guarded by
    kernel-checked [rfl] equalities) and of the two statements with [Finset.Ico]
    sums (kernel-checked normalization guards), related by [cs_ico] as in the
    accepted classic sum certificate.  Decision procedures are never unfolded.

    Statements: the source side is the exact elaborated type of the pinned lemma
    (via [type of]; the source proof is not used).  For
    [cumulative_service_le_task_cost], whose Rocq and Lean binder lists put
    [task_cost task_deadline : sporadic_task -> time] before the job type, the
    job type is fixed as an [eqType] with its canonical Lean instance and the two
    task parameters stay universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.

(* ------------------------------------------------------------------ *)
(** * Generic helpers *)

Lemma cs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cs_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cs_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cs_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cs_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma cs_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cs_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cs_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint cs_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cs_natl s') end.

Lemma cs_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cs_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cs_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cs_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cs_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cs_fun_canonical FR FL (HF : CsFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cs_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cs_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cs_foldr_add FL FR (cs_fun_canonical FR FL HF)).
  by rewrite cs_big_fold.
Qed.

Lemma cs_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cs_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cs_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cs_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cs_bigcat_nat_rel (A : Type) fR fL (Hf : CsNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicScheduleInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (co_iota_range (nR - mR) 0) co_map_inst1. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (co_cl_map_ext _ _ Hpt) (co_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) co_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cs_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cs_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cs_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cs_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicScheduleInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicScheduleInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cs_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicScheduleInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cs_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cs_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cs_forall_cover _ _ (CsParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CsSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cs_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cs_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cs_sched_canonical sR : CsSchedRel sR (cs_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cs_sched_surjective sL : CsSchedRel (cs_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cs_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cs_forall_cover _ _ CsSchedRel cs_sched_to_target cs_sched_to_source cs_sched_canonical cs_sched_surjective PR PL). Qed.
End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CsArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cs_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cs_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cs_arr_canonical aR : CsArrRel aR (cs_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cs_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cs_arr_surjective aL : CsArrRel (cs_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cs_arrives_in aR aL (Ha : CsArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cs_mem Job j _ _ (Ha tR tL Ht)). Qed.
End Arr.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.

Theorem Schedule_scheduled_on_correspondence j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cs_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cs_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Theorem Schedule_scheduled_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (Schedule_scheduled_on_correspondence j oR oL Ho tR tL Ht).
Qed.

Theorem Schedule_is_idle_correspondence oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Schedule.is_idle sR oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_is_idle Job dJ nL sL oL tL).
Proof.
  exact (cs_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR = None) (Lean.eq z (cl_opt None)))
           (cs_opt_eq_rel Job (sR oR tR) None)).
Qed.

Theorem Schedule_service_at_correspondence j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicScheduleInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := Schedule_scheduled_on_correspondence j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cs_service_at_fun j : CsFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (Schedule_service_at_correspondence j kR kL Hk). Qed.

Theorem Schedule_service_correspondence j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cs_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cs_service_at_fun j)). Qed.

Theorem Schedule_service_during_correspondence j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Schedule.service_during sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_during Job dJ nL sL j t1L t2L).
Proof. exact (cs_ico _ _ _ _ _ _ H1 H2 (cs_service_at_fun j)). Qed.

Theorem Schedule_completed_correspondence cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Schedule_service_correspondence j tR tL Ht)). Qed.

Theorem Schedule_pending_correspondence aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.pending aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_pending Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)
           (ct_bool_not _ _ (Schedule_completed_correspondence cR cL Hc j tR tL Ht))).
Qed.

Theorem Schedule_backlogged_correspondence aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.backlogged aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (Schedule_pending_correspondence aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (Schedule_scheduled_correspondence j tR tL Ht))).
Qed.

Theorem Schedule_carried_in_correspondence aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.carried_in aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_carried_in Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ (Ha j) Ht)
           (ct_bool_not _ _ (Schedule_completed_correspondence cR cL Hc j tR tL Ht))).
Qed.

Theorem Schedule_carried_out_correspondence aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  CtBoolRel (Schedule.carried_out aR cR sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_carried_out Job dJ aL cL nL sL j t1L t2L).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ (Ha j) H2)
           (ct_bool_not _ _ (Schedule_completed_correspondence cR cL Hc j t2R t2L H2))).
Qed.

Lemma cs_make_sequence (o : option Job) :
  ClListRel cid (make_sequence o) (I.Prosa_Classic_Util_Notation_make_sequence Job (cl_opt o)).
Proof. destruct o as [x|]; exact (@Lean.eq_refl _ _). Qed.

Theorem Schedule_jobs_scheduled_at_correspondence tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (Schedule.jobs_scheduled_at sR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_at Job dJ nL sL tL).
Proof.
  apply: (co_bigcat_rel Job nR nL Hn). intros oR oL Ho.
  exact (cs_trs (Hs oR oL Ho tR tL Ht)
           (fun z => ClListRel cid (make_sequence (sR oR tR)) (I.Prosa_Classic_Util_Notation_make_sequence Job z))
           (cs_make_sequence (sR oR tR))).
Qed.

Theorem Schedule_jobs_scheduled_between_correspondence t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (Schedule.jobs_scheduled_between sR t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_between Job dJ nL sL t1L t2L).
Proof.
  apply: cs_undup_rel. apply: (cs_bigcat_nat_rel Job (fun t => Schedule.jobs_scheduled_at sR t) _ _ _ _ _ _ H1 H2).
  intros kR kL Hk. exact (Schedule_jobs_scheduled_at_correspondence kR kL Hk).
Qed.

Theorem Schedule_sequential_jobs_correspondence :
  PropSPropRel (Schedule.sequential_jobs sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_sequential_jobs Job dJ nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: (co_forall_ord nR nL Hn) => o1R o1L H1. apply: (co_forall_ord nR nL Hn) => o2R o2L H2.
  apply: ct_imp.
  { exact (cs_tr (Hs o1R o1L H1 tR tL Ht) (fun z => PropSPropRel (sR o1R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cs_opt_eq_rel Job (sR o1R tR) (Some j))). }
  apply: ct_imp.
  { exact (cs_tr (Hs o2R o2L H2 tR tL Ht) (fun z => PropSPropRel (sR o2R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cs_opt_eq_rel Job (sR o2R tR) (Some j))). }
  exact (co_ord_eq_rel _ _ _ _ _ _ H1 H2).
Qed.

Theorem Schedule_jobs_must_arrive_to_execute_correspondence aR aL (Ha : CsParRel Job aR aL) :
  PropSPropRel (Schedule.jobs_must_arrive_to_execute aR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_must_arrive_to_execute Job dJ aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Schedule_scheduled_correspondence j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)).
Qed.

Theorem Schedule_completed_jobs_dont_execute_correspondence cR cL (Hc : CsParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (Schedule_service_correspondence j tR tL Ht) (Hc j)).
Qed.

Theorem Schedule_jobs_come_from_arrival_sequence_correspondence arrR arrL (Harr : CsArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Schedule_scheduled_correspondence j tR tL Ht)).
  exact (cs_arrives_in Job arrR arrL Harr j).
Qed.
End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Theorem ScheduleOfSporadicTask_task_scheduled_on_correspondence tsk oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfSporadicTask.task_scheduled_on job_task sR tsk oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_task_scheduled_on Task Job dT dJ job_task nL sL tsk oL tL).
Proof.
  refine (cs_trs (Hs oR oL Ho tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfSporadicTask.task_scheduled_on job_task sR tsk oR tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfSporadicTask.task_scheduled_on. destruct (sR oR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.

Theorem ScheduleOfSporadicTask_task_is_scheduled_correspondence tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfSporadicTask.task_is_scheduled job_task sR tsk tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_task_is_scheduled Task Job dT dJ job_task nL sL tsk tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ScheduleOfSporadicTask_task_scheduled_on_correspondence tsk oR oL Ho tR tL Ht).
Qed.

Theorem ScheduleOfSporadicTask_jobs_of_task_scheduled_between_correspondence tsk t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_jobs_of_task_scheduled_between
       Task Job dT dJ job_task nL sL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid (fun j => job_task j == tsk)
                            (fun j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk))
                            (fun j => ct_decide_eq Task (job_task j) tsk) _) _).
  exact (f_equal (I.List_filter Job (fun j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)))
           (Logic.eq_sym (cl_list_logic _ _ _ (Schedule_jobs_scheduled_between_correspondence Job nR nL Hn sR sL Hs _ _ _ _ H1 H2)))).
Qed.

Theorem ScheduleOfSporadicTask_jobs_of_same_task_dont_execute_in_parallel_correspondence :
  PropSPropRel (ScheduleOfSporadicTask.jobs_of_same_task_dont_execute_in_parallel job_task sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_jobs_of_same_task_dont_execute_in_parallel
       Task Job dT dJ job_task nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Schedule_scheduled_correspondence Job nR nL Hn sR sL Hs j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Schedule_scheduled_correspondence Job nR nL Hn sR sL Hs j' tR tL Ht)).
  exact (ct_eq_rel Job j j').
Qed.
End TaskDefs.

Theorem Schedule_processor_correspondence nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Theorem Schedule_schedule_correspondence (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CsSchedRel Job nR nL s (cs_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CsSchedRel Job nR nL (cs_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cs_sched_canonical Job nR nL Hn) (cs_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cs_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CsSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cs_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

Notation sa := Schedule_service_at_correspondence.
Notation sd := Schedule_service_during_correspondence.
Notation sc := Schedule_scheduled_correspondence.

Definition src_not_scheduled_no_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.not_scheduled_no_service Job)).
Definition tgt_not_scheduled_no_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_not_scheduled_no_service Job (ct_decidable_eq Job))).
Theorem Schedule_not_scheduled_no_service_correspondence (Job : eqType) :
  PropSPropRel (src_not_scheduled_no_service Job) (tgt_not_scheduled_no_service Job).
Proof.
  unfold src_not_scheduled_no_service, tgt_not_scheduled_no_service.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_bool_eq; first exact (ct_bool_not _ _ (sc Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_decide_eq_nat _ _ _ _ (sa Job nR nL Hn sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 0)).
Qed.

Definition src_cumulative_service_implies_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.cumulative_service_implies_service Job)).
Definition tgt_cumulative_service_implies_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_cumulative_service_implies_service Job (ct_decidable_eq Job))).
Theorem Schedule_cumulative_service_implies_service_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_implies_service Job) (tgt_cumulative_service_implies_service Job).
Proof.
  unfold src_cumulative_service_implies_service, tgt_cumulative_service_implies_service.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp.
  { exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (sd Job nR nL Hn sR sL Hs j _ _ _ _ H1 H2) (sub_nat_rel_canonical 0)))). }
  apply: ct_exists_nat => tR tL Ht.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (sa Job nR nL Hn sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 0)))).
Qed.

Definition src_service_implies_cumulative_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.service_implies_cumulative_service Job)).
Definition tgt_service_implies_cumulative_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_implies_cumulative_service Job (ct_decidable_eq Job))).
Theorem Schedule_service_implies_cumulative_service_correspondence (Job : eqType) :
  PropSPropRel (src_service_implies_cumulative_service Job) (tgt_service_implies_cumulative_service Job).
Proof.
  unfold src_service_implies_cumulative_service, tgt_service_implies_cumulative_service.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_imp.
  { exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (sa Job nR nL Hn sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 0)))). }
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (sd Job nR nL Hn sR sL Hs j _ _ _ _ H1 H2) (sub_nat_rel_canonical 0)))).
Qed.

Definition src_service_at_most_one (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.service_at_most_one Job)).
Definition tgt_service_at_most_one (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at_most_one Job (ct_decidable_eq Job))).
Theorem Schedule_service_at_most_one_correspondence (Job : eqType) :
  PropSPropRel (src_service_at_most_one Job) (tgt_service_at_most_one Job).
Proof.
  unfold src_service_at_most_one, tgt_service_at_most_one.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_sequential_jobs_correspondence Job nR nL Hn sR sL Hs).
  apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (sa Job nR nL Hn sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 1)).
Qed.

Definition src_cumulative_service_le_delta (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.cumulative_service_le_delta Job)).
Definition tgt_cumulative_service_le_delta (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_cumulative_service_le_delta Job (ct_decidable_eq Job))).
Theorem Schedule_cumulative_service_le_delta_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_le_delta Job) (tgt_cumulative_service_le_delta Job).
Proof.
  unfold src_cumulative_service_le_delta, tgt_cumulative_service_le_delta.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_sequential_jobs_correspondence Job nR nL Hn sR sL Hs).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd.
  exact (sub_nat_le_correspondence _ _ _ _ (sd Job nR nL Hn sR sL Hs j _ _ _ _ Ht (sub_add_correspondence _ _ _ _ Ht Hd)) Hd).
Qed.

Definition src_completion_monotonic (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.completion_monotonic Job)).
Definition tgt_completion_monotonic (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completion_monotonic Job (ct_decidable_eq Job))).
Theorem Schedule_completion_monotonic_correspondence (Job : eqType) :
  PropSPropRel (src_completion_monotonic Job) (tgt_completion_monotonic Job).
Proof.
  unfold src_completion_monotonic, tgt_completion_monotonic.
  apply: cs_forall_par => cR cL Hc.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (ct_bool_truth _ _ (Schedule_completed_correspondence Job nR nL Hn sR sL Hs cR cL Hc j tR tL Ht)).
  exact (ct_bool_truth _ _ (Schedule_completed_correspondence Job nR nL Hn sR sL Hs cR cL Hc j t'R t'L Ht')).
Qed.

Definition src_completed_implies_not_scheduled (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.completed_implies_not_scheduled Job)).
Definition tgt_completed_implies_not_scheduled (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_implies_not_scheduled Job (ct_decidable_eq Job))).
Theorem Schedule_completed_implies_not_scheduled_correspondence (Job : eqType) :
  PropSPropRel (src_completed_implies_not_scheduled Job) (tgt_completed_implies_not_scheduled Job).
Proof.
  unfold src_completed_implies_not_scheduled, tgt_completed_implies_not_scheduled.
  apply: cs_forall_par => cR cL Hc.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_completed_jobs_dont_execute_correspondence Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Schedule_completed_correspondence Job nR nL Hn sR sL Hs cR cL Hc j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (sc Job nR nL Hn sR sL Hs j tR tL Ht))).
Qed.

Definition src_cumulative_service_le_job_cost (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.cumulative_service_le_job_cost Job)).
Definition tgt_cumulative_service_le_job_cost (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_cumulative_service_le_job_cost Job (ct_decidable_eq Job))).
Theorem Schedule_cumulative_service_le_job_cost_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_le_job_cost Job) (tgt_cumulative_service_le_job_cost Job).
Proof.
  unfold src_cumulative_service_le_job_cost, tgt_cumulative_service_le_job_cost.
  apply: cs_forall_par => cR cL Hc.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_completed_jobs_dont_execute_correspondence Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  exact (sub_nat_le_correspondence _ _ _ _ (sd Job nR nL Hn sR sL Hs j _ _ _ _ Ht Ht') (Hc j)).
Qed.

Definition src_service_before_job_arrival_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.service_before_job_arrival_zero Job)).
Definition tgt_service_before_job_arrival_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_before_job_arrival_zero Job (ct_decidable_eq Job))).
Theorem Schedule_service_before_job_arrival_zero_correspondence (Job : eqType) :
  PropSPropRel (src_service_before_job_arrival_zero Job) (tgt_service_before_job_arrival_zero Job).
Proof.
  unfold src_service_before_job_arrival_zero, tgt_service_before_job_arrival_zero.
  apply: cs_forall_par => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_jobs_must_arrive_to_execute_correspondence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht (Ha j)).
  exact (sub_nat_eq_correspondence _ _ _ _ (sa Job nR nL Hn sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 0)).
Qed.

Definition src_cumulative_service_before_job_arrival_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.cumulative_service_before_job_arrival_zero Job)).
Definition tgt_cumulative_service_before_job_arrival_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_cumulative_service_before_job_arrival_zero Job (ct_decidable_eq Job))).
Theorem Schedule_cumulative_service_before_job_arrival_zero_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_before_job_arrival_zero Job) (tgt_cumulative_service_before_job_arrival_zero Job).
Proof.
  unfold src_cumulative_service_before_job_arrival_zero, tgt_cumulative_service_before_job_arrival_zero.
  apply: cs_forall_par => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_jobs_must_arrive_to_execute_correspondence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 (Ha j)).
  exact (sub_nat_eq_correspondence _ _ _ _ (cs_ico _ _ _ _ _ _ H1 H2 (cs_service_at_fun Job nR nL Hn sR sL Hs j))
           (sub_nat_rel_canonical 0)).
Qed.

Definition src_service_before_arrival_eq_service_during (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.service_before_arrival_eq_service_during Job)).
Definition tgt_service_before_arrival_eq_service_during (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_before_arrival_eq_service_during Job (ct_decidable_eq Job))).
Theorem Schedule_service_before_arrival_eq_service_during_correspondence (Job : eqType) :
  PropSPropRel (src_service_before_arrival_eq_service_during Job) (tgt_service_before_arrival_eq_service_during Job).
Proof.
  unfold src_service_before_arrival_eq_service_during, tgt_service_before_arrival_eq_service_during.
  apply: cs_forall_par => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_jobs_must_arrive_to_execute_correspondence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_nat => t0R t0L H0. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H0 (Ha j)).
  have Hend := sub_add_correspondence _ _ _ _ (Ha j) Ht.
  exact (sub_nat_eq_correspondence _ _ _ _ (cs_ico _ _ _ _ _ _ H0 Hend (cs_service_at_fun Job nR nL Hn sR sL Hs j))
           (cs_ico _ _ _ _ _ _ (Ha j) Hend (cs_service_at_fun Job nR nL Hn sR sL Hs j))).
Qed.

Definition src_scheduled_implies_pending (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.scheduled_implies_pending Job)).
Definition tgt_scheduled_implies_pending (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_implies_pending Job (ct_decidable_eq Job))).
Theorem Schedule_scheduled_implies_pending_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_implies_pending Job) (tgt_scheduled_implies_pending Job).
Proof.
  unfold src_scheduled_implies_pending, tgt_scheduled_implies_pending.
  apply: cs_forall_par => aR aL Ha. apply: cs_forall_par => cR cL Hc.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (Schedule_jobs_must_arrive_to_execute_correspondence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (Schedule_completed_jobs_dont_execute_correspondence Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (sc Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (Schedule_pending_correspondence Job nR nL Hn sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
Qed.

Definition src_mem_scheduled_jobs_eq_scheduled (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.mem_scheduled_jobs_eq_scheduled Job)).
Definition tgt_mem_scheduled_jobs_eq_scheduled (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_mem_scheduled_jobs_eq_scheduled Job (ct_decidable_eq Job))).
Theorem Schedule_mem_scheduled_jobs_eq_scheduled_correspondence (Job : eqType) :
  PropSPropRel (src_mem_scheduled_jobs_eq_scheduled Job) (tgt_mem_scheduled_jobs_eq_scheduled Job).
Proof.
  unfold src_mem_scheduled_jobs_eq_scheduled, tgt_mem_scheduled_jobs_eq_scheduled.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_bool_eq; last exact (sc Job nR nL Hn sR sL Hs j tR tL Ht).
  exact (ct_decide_bool _ _ _ (cs_mem Job j _ _ (Schedule_jobs_scheduled_at_correspondence Job nR nL Hn sR sL Hs tR tL Ht))).
Qed.

Definition src_scheduled_jobs_uniq (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.scheduled_jobs_uniq Job)).
Definition tgt_scheduled_jobs_uniq (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_jobs_uniq Job (ct_decidable_eq Job))).
Theorem Schedule_scheduled_jobs_uniq_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_jobs_uniq Job) (tgt_scheduled_jobs_uniq Job).
Proof.
  unfold src_scheduled_jobs_uniq, tgt_scheduled_jobs_uniq.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (Schedule_sequential_jobs_correspondence Job nR nL Hn sR sL Hs).
  apply: ct_forall_nat => tR tL Ht.
  exact (cs_uniq Job _ _ (Schedule_jobs_scheduled_at_correspondence Job nR nL Hn sR sL Hs tR tL Ht)).
Qed.

Definition src_num_scheduled_jobs_le_num_cpus (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedule.num_scheduled_jobs_le_num_cpus Job)).
Definition tgt_num_scheduled_jobs_le_num_cpus (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_num_scheduled_jobs_le_num_cpus Job (ct_decidable_eq Job))).
Theorem Schedule_num_scheduled_jobs_le_num_cpus_correspondence (Job : eqType) :
  PropSPropRel (src_num_scheduled_jobs_le_num_cpus Job) (tgt_num_scheduled_jobs_le_num_cpus Job).
Proof.
  unfold src_num_scheduled_jobs_le_num_cpus, tgt_num_scheduled_jobs_le_num_cpus.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _
           (cs_list_size Job _ _ (Schedule_jobs_scheduled_at_correspondence Job nR nL Hn sR sL Hs tR tL Ht)) Hn).
Qed.

Definition src_cumulative_service_le_task_cost (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> Time.time,
    ltac:(type_of_term (@ScheduleOfSporadicTask.cumulative_service_le_task_cost Task task_cost task_deadline Job)).
Definition tgt_cumulative_service_le_task_cost (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_cumulative_service_le_task_cost
                          Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem ScheduleOfSporadicTask_cumulative_service_le_task_cost_correspondence (Task Job : eqType) :
  PropSPropRel (src_cumulative_service_le_task_cost Task Job) (tgt_cumulative_service_le_task_cost Task Job).
Proof.
  unfold src_cumulative_service_le_task_cost, tgt_cumulative_service_le_task_cost.
  apply: cs_forall_par => tcR tcL Htc. apply: cs_forall_par => tdR tdL Htd.
  apply: cs_forall_par => cR cL Hc. apply: cs_forall_par => dR dL Hd. apply: ct_forall_identity => job_task.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (Schedule_completed_jobs_dont_execute_correspondence Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp.
  { apply: ct_and.
    { apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc j))).
      apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Hd j))).
      exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd j))). }
    apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j)))).
    exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). }
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  exact (sub_nat_le_correspondence _ _ _ _ (sd Job nR nL Hn sR sL Hs j _ _ _ _ Ht Ht') (Htc tsk)).
Qed.
