From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.seqset classic.model.time classic.model.schedule.global.basic.schedule
  classic.model.schedule.apa.affinity.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicAffinity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicAffinityBase ClassicAffinityList ClassicAffinityList1 ClassicAffinityOrd.

Module I := ImportedClassicAffinity.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/apa/affinity.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean
    [DecidableEq] instances given by the eqTypes' decision procedures
    ([ct_decidable_eq]); [job_task] identified; natural numbers (times,
    [num_cpus]) by [SubNatRel]; processors ['I_n] and [Fin n] by their values
    ([CoOrdRel]); affinities, the sequence-sets [{set 'I_n}] against the accepted
    v0.6 [Prosa.Util.Seqset.set (Fin n)], by their underlying sequences elementwise
    through the ordinal conversion ([CafRel]); task affinities pointwise; schedules
    pointwise on related processors and times with option values by the
    constructor map ([CsSchedRel], as for the accepted classic schedule
    certificate); all with two-way totals.

    Computation.  [[exists cpu, P cpu]] against [(List.finRange n).any P]
    ([co_exists_rel], through the exported kernel-checked [finRange_any]);
    [#|a|] against [(Finset.univ.filter (· ∈ a)).card]: MathComp [sum1_card] and
    [big_mkcond] on the source side, the exported kernel-checked [card_filter_sum]
    (the filtered [Finset] unfolds definitionally to the filtered [List.finRange],
    counted by structural recursion) and [fin_sum_range'] on the target side,
    related by [co_sum_rel].  Membership tests [decide (cpu ∈ a)] are related
    through the propositional correspondence of membership ([ct_decide_bool]); the
    Lean decision procedures are never unfolded.

    Statements: the source side is the exact elaborated type of the pinned lemma
    (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.

(* ------------------------------------------------------------------ *)
(** * Generic helpers (as in the accepted classic schedule certificate) *)

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

(* ------------------------------------------------------------------ *)
(** * Affinities: sets of ordinals against [Prosa.Util.Seqset.set (Fin n)] *)

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

(* ------------------------------------------------------------------ *)
(** * The classic schedule definitions this file uses *)

Section SchedDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Lemma caf_task_scheduled_on tsk oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
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
End SchedDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem Affinity_affinity_correspondence nR nL (Hn : SubNatRel nR nL) :
  And (forall a : Affinity.affinity nR, CafRel nR nL Hn a (caf_to_target nR nL Hn a))
      (forall a : I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL, CafRel nR nL Hn (caf_to_source nR nL Hn a) a).
Proof. exact (And_intro _ _ (caf_canonical nR nL Hn) (caf_surjective nR nL Hn)). Qed.

Section TaskAff.
Variables (Task : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation LTAff := (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task dT nL).

Definition CtafRel (aR : Affinity.task_affinity Task nR) (aL : LTAff) : SProp :=
  forall tsk, CafRel nR nL Hn (aR tsk) (aL tsk).

Theorem Affinity_task_affinity_correspondence :
  And (forall a : Affinity.task_affinity Task nR, CtafRel a (fun tsk => caf_to_target nR nL Hn (a tsk)))
      (forall a : LTAff, CtafRel (fun tsk => caf_to_source nR nL Hn (a tsk)) a).
Proof.
  apply: And_intro.
  - intros a tsk. exact (caf_canonical nR nL Hn (a tsk)).
  - intros a tsk. exact (caf_surjective nR nL Hn (a tsk)).
Qed.

Theorem Affinity_can_execute_on_correspondence aR aL (Ha : CtafRel aR aL) tsk oR oL (Ho : CoOrdRel nR nL oR oL) :
  CtBoolRel (Affinity.can_execute_on aR tsk oR)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_can_execute_on Task dT nL aL tsk oL).
Proof. exact (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ (Ha tsk) oR oL Ho)). Qed.
End TaskAff.

Section AffDefs.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.

Theorem Affinity_task_scheduled_on_affinity_correspondence (Task Job : eqType) (job_task : Job -> Task)
    sR sL (Hs : CsSchedRel Job nR nL sR sL) aR aL (Ha : CafRel nR nL Hn aR aL) tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Affinity.task_scheduled_on_affinity job_task sR aR tsk tR)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_scheduled_on_affinity
       Task (ct_decidable_eq Task) nL Job (ct_decidable_eq Job) job_task sL aL tsk tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ct_bool_and _ _ _ _ (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha oR oL Ho))
           (caf_task_scheduled_on Task Job nR nL sR sL Hs job_task tsk oR oL Ho tR tL Ht)).
Qed.

Theorem Affinity_is_subaffinity_correspondence a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) aR aL (Ha : CafRel nR nL Hn aR aL) :
  PropSPropRel (Affinity.is_subaffinity a'R aR)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_is_subaffinity nL a'L aL).
Proof.
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  exact (ct_imp _ _ _ _ (caf_mem nR nL Hn _ _ Ha' oR oL Ho) (caf_mem nR nL Hn _ _ Ha oR oL Ho)).
Qed.

Theorem Affinity_affinity_intersects_correspondence aR aL (Ha : CafRel nR nL Hn aR aL) a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) :
  CtBoolRel (Affinity.affinity_intersects aR a'R)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity_intersects nL aL a'L).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ct_bool_and _ _ _ _ (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha oR oL Ho))
           (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha' oR oL Ho))).
Qed.

(** [#|a|] against the cardinality of the filtered [Fin n] universe. *)
Lemma caf_card aR aL (Ha : CafRel nR nL Hn aR aL) :
  SubNatRel #|aR|
    (I.Finset_card_inst1 (Fin nL)
       (I.Finset_filter_inst1 (Fin nL)
          (fun x => I.Membership_mem_inst3 (Fin nL) (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL)
                      (I.Prosa_Util_Seqset_instMembershipSet_inst1 (Fin nL) (I.instDecidableEqFin nL)) aL x)
          (fun a => I.Prosa_Classic_Util_Seqset_memDecidable_inst1 (Fin nL) (I.instDecidableEqFin nL) a aL)
          (I.Finset_univ_inst1 (Fin nL) (I.Fin_fintype nL)))).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicAffinityInterface_card_filter_sum nL
             (fun x => I.Membership_mem_inst3 (Fin nL) (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL)
                         (I.Prosa_Util_Seqset_instMembershipSet_inst1 (Fin nL) (I.instDecidableEqFin nL)) aL x)
             (fun a => I.Prosa_Classic_Util_Seqset_memDecidable_inst1 (Fin nL) (I.instDecidableEqFin nL) a aL))).
  have E : #|aR| = \sum_(i < nR) (if i \in aR then 1 else 0) by rewrite -sum1_card big_mkcond.
  rewrite E. apply: imported_eq_to_coq_eq.
  apply: (co_sum_rel nR nL Hn) => oR oL Ho.
  have H := ct_decide_bool _ _ (I.Prosa_Classic_Util_Seqset_memDecidable_inst1 (Fin nL) (I.instDecidableEqFin nL) oL aL)
              (caf_mem nR nL Hn _ _ Ha oR oL Ho).
  rewrite (ct_bool_rel_logic _ _ H). destruct (oR \in aR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.
End AffDefs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_leq_subaffinity : Prop := ltac:(type_of_term @Affinity.leq_subaffinity).
Definition tgt_leq_subaffinity : SProp := ltac:(type_of_term @I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_leq_subaffinity).

Theorem Affinity_leq_subaffinity_correspondence : PropSPropRel src_leq_subaffinity tgt_leq_subaffinity.
Proof.
  unfold src_leq_subaffinity, tgt_leq_subaffinity.
  apply: ct_forall_nat => nR nL Hn.
  apply: (caf_forall nR nL Hn) => a'R a'L Ha'. apply: (caf_forall nR nL Hn) => aR aL Ha.
  apply: ct_imp; first exact (Affinity_is_subaffinity_correspondence nR nL Hn _ _ Ha' _ _ Ha).
  exact (sub_nat_le_correspondence _ _ _ _ (caf_card nR nL Hn _ _ Ha') (caf_card nR nL Hn _ _ Ha)).
Qed.
