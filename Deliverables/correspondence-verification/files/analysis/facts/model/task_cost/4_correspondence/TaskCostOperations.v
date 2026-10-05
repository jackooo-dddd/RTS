From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.facts.model.task_cost.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskCost ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TaskCostBaseAdapter TaskCostClasses.

(** Reused Nat/Bool/equality patterns instantiated for this actual import.
    Class field relations are related-input conditions, not axioms. *)

Definition tc_target_false_elim (Q : SProp)
    (H : ImportedTaskCost.False) : Q := match H return Q with end.

Lemma tc_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedTaskCost.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  TcBoolRel b (ImportedTaskCost.Decidable_decide Q d).
Proof.
  intro Hrel. unfold TcBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (tc_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (tc_target_false_elim _ (tc_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition tc_target_decide_eq (T : eqType) (x y : T) :
    ImportedTaskCost.Bool :=
  ImportedTaskCost.Decidable_decide (Lean.eq x y)
    (tc_decidable_eq T x y).

Lemma tc_decide_eq_related (T : eqType) (x y : T) :
  TcBoolRel (x == y) (tc_target_decide_eq T x y).
Proof.
  apply tc_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - move/eqP => Heq. exact (coq_eq_to_imported_eq _ _ Heq).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq _ _ Heq).
Qed.

Definition tc_target_le (a b : Lean.Nat) : SProp :=
  ImportedTaskCost.LE_le_inst1 Lean.Nat ImportedTaskCost.instLENat a b.

Definition tc_target_lt (a b : Lean.Nat) : SProp :=
  ImportedTaskCost.LT_lt_inst1 Lean.Nat ImportedTaskCost.instLTNat a b.

Definition tc_target_decide_le (a b : Lean.Nat) : ImportedTaskCost.Bool :=
  ImportedTaskCost.Decidable_decide (tc_target_le a b)
    (ImportedTaskCost.Nat_decLe a b).

Definition tc_target_decide_lt (a b : Lean.Nat) : ImportedTaskCost.Bool :=
  ImportedTaskCost.Decidable_decide (tc_target_lt a b)
    (ImportedTaskCost.Nat_decLt a b).

Lemma tc_decide_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  TcBoolRel (leq aR bR) (tc_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply tc_decide_bool_correspondence.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma tc_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  TcBoolRel (ltn aR bR) (tc_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply tc_decide_bool_correspondence.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma tc_bool_and_related aR aL bR bL :
  TcBoolRel aR aL -> TcBoolRel bR bL ->
  TcBoolRel (aR && bR) (ImportedTaskCost.Bool_and aL bL).
Proof.
  intros Ha Hb. unfold TcBoolRel in *.
  destruct aR, bR; cbn;
    exact (sub_imported_eq_congr2 ImportedTaskCost.Bool_and _ _ _ _ Ha Hb).
Qed.

Section CostPredicates.
  Context (Job Task : eqType).
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL : ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
    Job (tc_decidable_eq Job) Task (tc_decidable_eq Task).
  Hypothesis HjobTask : TcJobTaskRel Job Task jobTaskR jobTaskL.
  Variable jobCostR : prosa.behavior.job.JobCost Job.
  Variable jobCostL : ImportedTaskCost.Prosa_Behavior_Job_JobCost
    Job (tc_decidable_eq Job).
  Hypothesis HjobCost : TcJobCostRel Job jobCostR jobCostL.
  Variable taskCostR : prosa.model.task.concept.TaskCost Task.
  Variable taskCostL : ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
    Task (tc_decidable_eq Task).
  Hypothesis HtaskCost : TcTaskCostRel Task taskCostR taskCostL.

  Lemma tc_job_task_cost_related (j : Job) :
    SubNatRel
      (@prosa.model.task.concept.task_cost Task taskCostR
        (@prosa.model.task.concept.job_task Job Task jobTaskR j))
      (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
        Task (tc_decidable_eq Task) taskCostL
        (ImportedTaskCost.Prosa_Model_Task_Concept_JobTask_job_task
          Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)
          jobTaskL j)).
  Proof.
    exact (sub_imported_eq_trans _ _ _
      (HtaskCost (@prosa.model.task.concept.job_task Job Task jobTaskR j))
      (sub_imported_eq_congr
        (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
          Task (tc_decidable_eq Task) taskCostL) _ _ (HjobTask j))).
  Qed.

  Lemma tc_job_of_task_related (tsk : Task) (j : Job) :
    TcBoolRel
      (@prosa.model.task.concept.job_of_task Job Task jobTaskR tsk j)
      (ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task
        Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)
        jobTaskL tsk j).
  Proof.
    cbn [ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task].
    exact (sub_imported_eq_trans _ _ _
      (tc_decide_eq_related Task
        (@prosa.model.task.concept.job_task Job Task jobTaskR j) tsk)
      (sub_imported_eq_congr
        (fun t => tc_target_decide_eq Task t tsk) _ _ (HjobTask j))).
  Qed.

  Lemma tc_job_cost_positive_related (j : Job) :
    TcBoolRel
      (@prosa.model.job.properties.job_cost_positive Job jobCostR j)
      (ImportedTaskCost.Prosa_Model_Job_Properties_job_cost_positive
        Job (tc_decidable_eq Job) jobCostL j).
  Proof.
    cbn [ImportedTaskCost.Prosa_Model_Job_Properties_job_cost_positive].
    exact (tc_decide_lt_related 0 Lean.Nat_zero
      (@prosa.behavior.job.job_cost Job jobCostR j)
      (ImportedTaskCost.Prosa_Behavior_Job_JobCost_job_cost
        Job (tc_decidable_eq Job) jobCostL j)
      (sub_nat_rel_canonical 0) (HjobCost j)).
  Qed.

  Lemma tc_valid_job_cost_related (j : Job) :
    TcBoolRel
      (@prosa.model.task.concept.valid_job_cost
        Task taskCostR Job jobTaskR jobCostR j)
      (ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost
        Task (tc_decidable_eq Task) taskCostL
        Job (tc_decidable_eq Job) jobTaskL jobCostL j).
  Proof.
    cbn [ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost].
    exact (tc_decide_le_related _ _ _ _
      (HjobCost j) (tc_job_task_cost_related j)).
  Qed.

  Lemma tc_valid_job_and_related (tsk : Task) (j : Job) :
    TcBoolRel
      (@prosa.model.task.concept.job_of_task Job Task jobTaskR tsk j &&
       @prosa.model.task.concept.valid_job_cost
         Task taskCostR Job jobTaskR jobCostR j)
      (ImportedTaskCost.Bool_and
        (ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task
          Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)
          jobTaskL tsk j)
        (ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost
          Task (tc_decidable_eq Task) taskCostL
          Job (tc_decidable_eq Job) jobTaskL jobCostL j)).
  Proof.
    exact (tc_bool_and_related _ _ _ _
      (tc_job_of_task_related tsk j) (tc_valid_job_cost_related j)).
  Qed.
End CostPredicates.

Print Assumptions tc_job_of_task_related.
Print Assumptions tc_job_cost_positive_related.
Print Assumptions tc_valid_job_cost_related.
Print Assumptions tc_valid_job_and_related.
