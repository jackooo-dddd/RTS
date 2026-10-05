(* Re-bound copy of accepted certificates/analysis_transform_edf_trans/EdfTransCorrespondence.v: the imported
   module name differs, and its restated ideal-state block (id_lean_transport, id_nat_input, id_opt_to_imported,
   IdOptRel, IdScheduleRel) is replaced by the import of the accepted IdealUniSchedulerCorrespondence, whose
   definitions are identical; all other blocks are byte-identical. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import EdfTransSemanticSource.
From prosa Require Import model.processor.ideal analysis.transform.swap.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsEdfOpt ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence.

Module I := ImportedFactsEdfOpt.
Module S := EdfTransSemanticSource.EdfTransSemanticSource.
Module G := GeneratedSearchArgSource.GeneratedSearchArgSource.
Module P := TransformPrefixSemanticSource.TransformPrefixSemanticSource.

(** Definition certificates for [analysis/transform/edf_trans.v].

    Source side: the extracted byte-identical definition blocks (their
    [search_arg] bound to the accepted generated definition source, their
    [prefix_map] to the accepted extracted prefix source, [swapped] and the
    ideal processor to the pinned sources); target side: the compiled Lean
    definitions.  The processor model is fixed to the ideal uniprocessor on
    both sides: states are related by the accepted constructor-preserving
    Option map ([IdOptRel]), schedules pointwise ([IdScheduleRel]);
    [job_deadline] is related pointwise by [SubNatRel], [job_arrival] by
    [ArJobArrivalRel], instants by [SubNatRel]; jobs are identity carriers.
    The structurally recursive [search_arg] and [prefix_map] and the
    [replace_at] underlying [swapped] are related by induction and case
    analysis closed by kernel-checked Lean equations at the ideal processor,
    exported with the artifact.  No source or target theorem is used. *)

Lemma fet_src_transport {A : Type} (P : A -> SProp) (x y : A) :
  Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma fet_bool_true (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> bR = true -> Lean.eq bL I.Bool_true.
Proof. intros H E. subst bR. exact (sub_imported_eq_sym _ _ H). Qed.

Lemma fet_bool_false (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> bR = false -> Lean.eq bL I.Bool_false.
Proof. intros H E. subst bR. exact (sub_imported_eq_sym _ _ H). Qed.

(** ** Ideal states and schedules: [IdOptRel], [IdScheduleRel], [id_lean_transport] and [id_nat_input] are the
    identical definitions of the accepted [IdealUniSchedulerCorrespondence] (imported above) *)

Lemma fet_bool_false_not (b : bool) (Q : SProp) :
  PropSPropRel (is_true b) Q -> b = false -> I.Not Q.
Proof.
  intros H E HL. have Hb := sprop_to_prop _ _ H HL. rewrite E in Hb. discriminate Hb.
Qed.

Definition fet_bool_cases (c : bool) : Specif.sumbool (Logic.eq c true) (Logic.eq c false) :=
  match c as c' return Specif.sumbool (Logic.eq c' true) (Logic.eq c' false) with
  | true => @Specif.left (Logic.eq true true) (Logic.eq true false) (@Logic.eq_refl bool true)
  | false => @Specif.right (Logic.eq false true) (Logic.eq false false) (@Logic.eq_refl bool false)
  end.

Definition fet_opt_cases {T : Type} (o : option T) :
    Specif.sumor (Specif.sig (fun x : T => Logic.eq o (Some x))) (Logic.eq o None) :=
  match o as o' return Specif.sumor (Specif.sig (fun x : T => Logic.eq o' (Some x))) (Logic.eq o' None) with
  | Some x => @Specif.inleft _ (Logic.eq (Some x) None)
      (@Specif.exist T (fun y : T => Logic.eq (Some x) (Some y)) x (@Logic.eq_refl (option T) (Some x)))
  | None => @Specif.inright (Specif.sig (fun y : T => Logic.eq None (Some y))) _ (@Logic.eq_refl (option T) None)
  end.

(** ** Options of instants *)

Definition fet_optnat_to_imported (o : option nat) : I.Option_inst1 Lean.Nat :=
  match o with
  | None => I.Option_none_inst1 Lean.Nat
  | Some n => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported n)
  end.

Definition FetOptNatRel (oR : option nat) (oL : I.Option_inst1 Lean.Nat) : SProp :=
  Lean.eq (fet_optnat_to_imported oR) oL.

Section Ideal.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let StL := I.Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job dJ PSL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Let ONE := sub_nat_rel_canonical (S O).

  (** *** State predicates *)

  Lemma fet_deadline_of_state_related (sR : option Job) :
    SubNatRel (oapp (@prosa.behavior.job.job_deadline Job dlR) O sR)
      (I.Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job dJ
        (fun _ : StL => I.Prosa_Behavior_Time_instant) (id_opt_to_imported sR)
        (fun _ : I.Unit => I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_instant 0 (I.instOfNatNat 0))
        (fun j : Job => I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j)).
  Proof.
    destruct sR as [j|].
    - exact (Hdl j).
    - exact (sub_nat_rel_canonical O).
  Qed.

  Theorem earlier_deadline_correspondence (s1R s2R : option Job) (s1L s2L : StL) :
    IdOptRel s1R s1L -> IdOptRel s2R s2L ->
    SvcBoolRel (@S.earlier_deadline Job dlR s1R s2R)
      (I.Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job dJ dlL s1L s2L).
  Proof.
    intros H1 H2.
    refine (id_lean_transport (fun x => SvcBoolRel (@S.earlier_deadline Job dlR s1R s2R)
      (I.Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job dJ dlL x s2L)) _ _ H1 _).
    refine (id_lean_transport (fun y => SvcBoolRel (@S.earlier_deadline Job dlR s1R s2R)
      (I.Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job dJ dlL (id_opt_to_imported s1R) y)) _ _ H2 _).
    exact (svc_decide_le_related _ _ _ _ (fet_deadline_of_state_related s1R) (fet_deadline_of_state_related s2R)).
  Qed.

  Theorem relevant_pstate_correspondence (tR : nat) (tL : Lean.Nat) (sR : option Job) (sL : StL) :
    SubNatRel tR tL -> IdOptRel sR sL ->
    SvcBoolRel (@S.relevant_pstate Job jaR tR sR)
      (I.Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job dJ jaL tL sL).
  Proof.
    intros Ht Hs.
    refine (id_lean_transport (fun x => SvcBoolRel (@S.relevant_pstate Job jaR tR sR)
      (I.Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job dJ jaL tL x)) _ _ Hs _).
    destruct sR as [j|].
    - exact (svc_decide_le_related _ _ _ _ (Hja j) Ht).
    - exact (@Lean.eq_refl _ _).
  Qed.

  (** *** search_arg at the ideal processor *)

  Let HL1 (n : Lean.Nat) : Lean.Nat :=
    I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) n
      (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)).

  Section SearchArg.
    Variable fR : nat -> option Job.
    Variable fL : Lean.Nat -> StL.
    Hypothesis Hf : forall nR nL, SubNatRel nR nL -> IdOptRel (fR nR) (fL nL).
    Variable PR : option Job -> bool.
    Variable PL : StL -> I.Bool.
    Hypothesis HP : forall sR sL, IdOptRel sR sL -> SvcBoolRel (PR sR) (PL sL).
    Variable RR : option Job -> option Job -> bool.
    Variable RL : StL -> StL -> I.Bool.
    Hypothesis HR : forall s1R s1L s2R s2L, IdOptRel s1R s1L -> IdOptRel s2R s2L ->
      SvcBoolRel (RR s1R s2R) (RL s1L s2L).
    Variable aR : nat.
    Variable aL : Lean.Nat.
    Hypothesis Ha : SubNatRel aR aL.

    Let SAL b := I.Prosa_Util_SearchArg_search_arg StL fL PL RL aL b.

    Lemma fet_src_search_arg_succ (b : nat) :
      G.search_arg fR PR RR aR b.+1 =
        (if ltn aR b.+1 then
           match G.search_arg fR PR RR aR b with
           | None => if PR (fR b) then Some b else None
           | Some x => if PR (fR b) && RR (fR b) (fR x) then Some b else Some x
           end
         else None).
    Proof. reflexivity. Qed.

    Lemma fet_search_arg_canonical (bR : nat) :
      FetOptNatRel (G.search_arg fR PR RR aR bR) (SAL (sub_nat_to_imported bR)).
    Proof.
      induction bR as [|b IH].
      - exact (sub_imported_eq_sym _ _
          (I.Prosa_Validation_EdfTransInterface_production_search_arg_zero Job dJ fL PL RL aL)).
      - have Hb := sub_nat_rel_canonical b.
        have Hb1 : SubNatRel b.+1 (HL1 (sub_nat_to_imported b)) :=
          fet_src_transport (fun x => SubNatRel x (HL1 (sub_nat_to_imported b))) _ _ (addn1 b)
            (sub_add_correspondence _ _ _ _ Hb (@Lean.eq_refl _ _)).
        refine (id_lean_transport (fun y => FetOptNatRel (G.search_arg fR PR RR aR b.+1) (SAL y))
          _ _ (sub_imported_eq_sym _ _ Hb1) _).
        have Hlt := sub_nat_lt_correspondence _ _ _ _ Ha Hb1.
        destruct (fet_bool_cases (ltn aR b.+1)) as [Elt|Elt].
        + have HltL := prop_to_sprop _ _ Hlt Elt.
          destruct (fet_opt_cases (G.search_arg fR PR RR aR b)) as [[x Eb]|Eb].
          * have HsL := sub_imported_eq_sym _ _
              (fet_src_transport (fun o => FetOptNatRel o (SAL (sub_nat_to_imported b))) _ _ Eb IH).
            have Hx := sub_nat_rel_canonical x.
            have Hc := ar_bool_and_related _ _ _ _ (HP _ _ (Hf _ _ Hb))
              (HR _ _ _ _ (Hf _ _ Hb) (Hf _ _ Hx)).
            destruct (fet_bool_cases (PR (fR b) && RR (fR b) (fR x))) as [Ec|Ec].
            -- refine (fet_src_transport (fun o => FetOptNatRel o (SAL (HL1 (sub_nat_to_imported b)))) (Some b) _ _ _).
               ++ by rewrite fet_src_search_arg_succ Elt Eb Ec.
               ++ exact (sub_imported_eq_sym _ _
                    (I.Prosa_Validation_EdfTransInterface_production_search_arg_succ_some_true Job dJ fL PL RL aL
                      _ _ HltL HsL (fet_bool_true _ _ Hc Ec))).
            -- refine (fet_src_transport (fun o => FetOptNatRel o (SAL (HL1 (sub_nat_to_imported b)))) (Some x) _ _ _).
               ++ by rewrite fet_src_search_arg_succ Elt Eb Ec.
               ++ exact (sub_imported_eq_sym _ _
                    (I.Prosa_Validation_EdfTransInterface_production_search_arg_succ_some_false Job dJ fL PL RL aL
                      _ _ HltL HsL (fet_bool_false _ _ Hc Ec))).
          * have HnL := sub_imported_eq_sym _ _
              (fet_src_transport (fun o => FetOptNatRel o (SAL (sub_nat_to_imported b))) _ _ Eb IH).
            have Hc := HP _ _ (Hf _ _ Hb).
            destruct (fet_bool_cases (PR (fR b))) as [Ep|Ep].
            -- refine (fet_src_transport (fun o => FetOptNatRel o (SAL (HL1 (sub_nat_to_imported b)))) (Some b) _ _ _).
               ++ by rewrite fet_src_search_arg_succ Elt Eb Ep.
               ++ exact (sub_imported_eq_sym _ _
                    (I.Prosa_Validation_EdfTransInterface_production_search_arg_succ_none_true Job dJ fL PL RL aL
                      _ HltL HnL (fet_bool_true _ _ Hc Ep))).
            -- refine (fet_src_transport (fun o => FetOptNatRel o (SAL (HL1 (sub_nat_to_imported b)))) None _ _ _).
               ++ by rewrite fet_src_search_arg_succ Elt Eb Ep.
               ++ exact (sub_imported_eq_sym _ _
                    (I.Prosa_Validation_EdfTransInterface_production_search_arg_succ_none_false Job dJ fL PL RL aL
                      _ HltL HnL (fet_bool_false _ _ Hc Ep))).
        + have HnlL := fet_bool_false_not _ _ Hlt Elt.
          refine (fet_src_transport (fun o => FetOptNatRel o (SAL (HL1 (sub_nat_to_imported b)))) None _ _ _).
          * by rewrite fet_src_search_arg_succ Elt.
          * exact (sub_imported_eq_sym _ _
              (I.Prosa_Validation_EdfTransInterface_production_search_arg_succ_ge Job dJ fL PL RL aL _ HnlL)).
    Qed.

    Theorem fet_search_arg_related (bR : nat) (bL : Lean.Nat) :
      SubNatRel bR bL -> FetOptNatRel (G.search_arg fR PR RR aR bR) (SAL bL).
    Proof.
      intro Hb.
      exact (id_lean_transport (fun y => FetOptNatRel (G.search_arg fR PR RR aR bR) (SAL y)) _ _ Hb
        (fet_search_arg_canonical bR)).
    Qed.
  End SearchArg.

  (** *** find_swap_candidate *)

  Lemma fet_find_match_related (o : option nat) :
    SubNatRel (if o is Some t then t else O)
      (I.Prosa_Analysis_Transform_EdfTrans_find_swap_candidate_match_1 (fun _ : I.Option_inst1 Lean.Nat => Lean.Nat)
        (fet_optnat_to_imported o) (fun a : Lean.Nat => a)
        (fun _ : I.Unit => I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))).
  Proof.
    destruct o as [t|].
    - exact (sub_nat_rel_canonical t).
    - exact (sub_nat_rel_canonical O).
  Qed.

  Theorem find_swap_candidate_correspondence (schedR : SchedR) (schedL : SchedL)
      (t1R : nat) (t1L : Lean.Nat) (j : Job) :
    IdScheduleRel Job schedR schedL -> SubNatRel t1R t1L ->
    SubNatRel (@S.find_swap_candidate Job dlR jaR schedR t1R j)
      (I.Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job dJ dlL jaL schedL t1L j).
  Proof.
    intros Hs Ht.
    have HSA := fet_search_arg_related schedR schedL Hs _ _
      (fun sR sL Hx => relevant_pstate_correspondence _ _ _ _ Ht Hx)
      _ _ (fun s1R s1L s2R s2L H1 H2 => earlier_deadline_correspondence _ _ _ _ H1 H2)
      _ _ Ht _ _ (Hdl j).
    exact (id_lean_transport (fun y => SubNatRel
        (if G.search_arg schedR (@S.relevant_pstate Job jaR t1R) (@S.earlier_deadline Job dlR) t1R
              (@prosa.behavior.job.job_deadline Job dlR j) is Some t then t else O)
        (I.Prosa_Analysis_Transform_EdfTrans_find_swap_candidate_match_1 (fun _ : I.Option_inst1 Lean.Nat => Lean.Nat)
          y (fun a : Lean.Nat => a) (fun _ : I.Unit => I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))))
      _ _ HSA (fet_find_match_related _)).
  Qed.

  (** *** replace_at and swapped *)

  Lemma fet_nat_not_eq (tR t'R : nat) (tL t'L : Lean.Nat) :
    SubNatRel tR tL -> SubNatRel t'R t'L -> t'R <> tR -> I.Not (Lean.eq tL t'L).
  Proof.
    intros Ht Ht' NE. unfold I.Not. intro EL.
    refine (match NE _ return I.False with end).
    rewrite -(id_nat_input _ _ Ht) -(id_nat_input _ _ Ht').
    exact (Logic.eq_sym (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ EL))).
  Qed.

  Lemma fet_replace_at_related (sR : SchedR) (sL : SchedL) (t'R : nat) (t'L : Lean.Nat)
      (nsR : option Job) (nsL : StL) :
    IdScheduleRel Job sR sL -> SubNatRel t'R t'L -> IdOptRel nsR nsL ->
    IdScheduleRel Job (@prosa.analysis.transform.swap.replace_at Job PSR sR t'R nsR)
      (I.Prosa_Analysis_Transform_Swap_replace_at_inst4 Job dJ PSL sL t'L nsL).
  Proof.
    intros Hs Ht' Hns tR tL Ht.
    destruct (@eqP nat t'R tR) as [E|NE].
    - refine (fet_src_transport (fun o => IdOptRel o _) nsR _ _ _).
      + subst tR. by rewrite /prosa.analysis.transform.swap.replace_at eqxx.
      + subst tR.
        exact (sub_imported_eq_trans _ _ _ Hns (sub_imported_eq_sym _ _
          (I.Prosa_Validation_EdfTransInterface_production_replace_at_same Job dJ sL t'L nsL tL
            (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ht) Ht')))).
    - refine (fet_src_transport (fun o => IdOptRel o _) (sR tR) _ _ _).
      + move/eqP: NE => NE. by rewrite /prosa.analysis.transform.swap.replace_at (negbTE NE).
      + exact (sub_imported_eq_trans _ _ _ (Hs tR tL Ht) (sub_imported_eq_sym _ _
          (I.Prosa_Validation_EdfTransInterface_production_replace_at_other Job dJ sL t'L nsL tL
            (fet_nat_not_eq _ _ _ _ Ht Ht' NE)))).
  Qed.

  Lemma fet_swapped_related (sR : SchedR) (sL : SchedL) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    IdScheduleRel Job sR sL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    IdScheduleRel Job (@prosa.analysis.transform.swap.swapped Job PSR sR t1R t2R)
      (I.Prosa_Analysis_Transform_Swap_swapped_inst4 Job dJ PSL sL t1L t2L).
  Proof.
    intros Hs H1 H2.
    exact (fet_replace_at_related _ _ _ _ _ _
      (fet_replace_at_related _ _ _ _ _ _ Hs H1 (Hs _ _ H2)) H2 (Hs _ _ H1)).
  Qed.

  (** *** make_edf_at *)

  Theorem make_edf_at_correspondence (schedR : SchedR) (schedL : SchedL) (t1R : nat) (t1L : Lean.Nat) :
    IdScheduleRel Job schedR schedL -> SubNatRel t1R t1L ->
    IdScheduleRel Job (@S.make_edf_at Job dlR jaR schedR t1R)
      (I.Prosa_Analysis_Transform_EdfTrans_make_edf_at Job dJ dlL jaL schedL t1L).
  Proof.
    intros Hs Ht.
    unfold S.make_edf_at.
    cbn [I.Prosa_Analysis_Transform_EdfTrans_make_edf_at].
    refine (id_lean_transport (fun y => IdScheduleRel Job
      (match schedR t1R with
       | None => schedR
       | Some j => let t2 := @S.find_swap_candidate Job dlR jaR schedR t1R j in
                   @prosa.analysis.transform.swap.swapped Job PSR schedR t1R t2
       end)
      (I.Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job dJ (fun _ : StL => SchedL) y
        (fun _ : I.Unit => schedL)
        (fun j : Job =>
          let t2 := I.Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job dJ dlL jaL schedL t1L j in
          I.Prosa_Analysis_Transform_Swap_swapped_inst4 Job dJ PSL schedL t1L t2))) _ _ (Hs _ _ Ht) _).
    destruct (schedR t1R) as [j|].
    - exact (fet_swapped_related _ _ _ _ _ _ Hs Ht
        (find_swap_candidate_correspondence _ _ _ _ j Hs Ht)).
    - exact Hs.
  Qed.

  (** *** prefix_map, edf_transform_prefix and edf_transform *)

  Section Prefix.
    Variable fR : SchedR -> nat -> SchedR.
    Variable fL : SchedL -> I.Prosa_Behavior_Time_instant -> SchedL.
    Hypothesis Hfun : forall sR sL tR tL, IdScheduleRel Job sR sL -> SubNatRel tR tL ->
      IdScheduleRel Job (fR sR tR) (fL sL tL).
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IdScheduleRel Job sR sL.

    Let PML h := I.Prosa_Analysis_Transform_Prefix_prefix_map_inst4 Job dJ PSL sL fL h.

    Lemma fet_prefix_map_canonical (hR : nat) :
      IdScheduleRel Job (@P.prefix_map Job PSR sR fR hR) (PML (sub_nat_to_imported hR)).
    Proof.
      induction hR as [|h IH].
      - exact (id_lean_transport (fun y => IdScheduleRel Job sR y) _ _
          (sub_imported_eq_sym _ _
            (I.Prosa_Validation_EdfTransInterface_production_prefix_map_zero Job dJ sL fL)) Hs).
      - exact (id_lean_transport (fun y => IdScheduleRel Job (fR (@P.prefix_map Job PSR sR fR h) h) y) _ _
          (sub_imported_eq_sym _ _
            (I.Prosa_Validation_EdfTransInterface_production_prefix_map_succ Job dJ sL fL
              (sub_nat_to_imported h)))
          (Hfun _ _ _ _ IH (sub_nat_rel_canonical h))).
    Qed.

    Lemma fet_prefix_map_related (hR : nat) (hL : Lean.Nat) :
      SubNatRel hR hL -> IdScheduleRel Job (@P.prefix_map Job PSR sR fR hR) (PML hL).
    Proof.
      intro Hh.
      exact (id_lean_transport (fun y => IdScheduleRel Job (@P.prefix_map Job PSR sR fR hR) (PML y)) _ _ Hh
        (fet_prefix_map_canonical hR)).
    Qed.
  End Prefix.

  Theorem edf_transform_prefix_correspondence (schedR : SchedR) (schedL : SchedL) (hR : nat) (hL : Lean.Nat) :
    IdScheduleRel Job schedR schedL -> SubNatRel hR hL ->
    IdScheduleRel Job (@S.edf_transform_prefix Job dlR jaR schedR hR)
      (I.Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job dJ dlL jaL schedL hL).
  Proof.
    intros Hs Hh.
    unfold S.edf_transform_prefix.
    cbn [I.Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix].
    exact (fet_prefix_map_related _ _ (fun sR sL tR tL H1 H2 => make_edf_at_correspondence sR sL tR tL H1 H2)
      _ _ Hs _ _ Hh).
  Qed.

  Theorem edf_transform_correspondence (schedR : SchedR) (schedL : SchedL) (tR : nat) (tL : Lean.Nat) :
    IdScheduleRel Job schedR schedL -> SubNatRel tR tL ->
    IdOptRel (@S.edf_transform Job dlR jaR schedR tR)
      (I.Prosa_Analysis_Transform_EdfTrans_edf_transform Job dJ dlL jaL schedL tL).
  Proof.
    intros Hs Ht.
    unfold S.edf_transform.
    cbn [I.Prosa_Analysis_Transform_EdfTrans_edf_transform].
    have Ht1 : SubNatRel tR.+1 (HL1 tL) :=
      fet_src_transport (fun x => SubNatRel x (HL1 tL)) _ _ (addn1 tR)
        (sub_add_correspondence _ _ _ _ Ht (@Lean.eq_refl _ _)).
    exact (edf_transform_prefix_correspondence _ _ _ _ Hs Ht1 _ _ Ht).
  Qed.
End Ideal.
