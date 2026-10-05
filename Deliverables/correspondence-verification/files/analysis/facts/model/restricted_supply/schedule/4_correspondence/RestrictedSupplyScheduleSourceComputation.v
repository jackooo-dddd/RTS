From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.facts.model.restricted_supply.schedule.

Local Transparent prosa.behavior.schedule.scheduled_on
  prosa.behavior.schedule.supply_on
  prosa.behavior.schedule.service_on.

(** These computations use the official source processor fields, not any of the
    three target source theorem proofs. *)
Lemma rss_source_scheduled_in_iff_on (Job : eqType) (j : Job)
    (s : @prosa.model.processor.restricted_supply.processor_state Job) :
  is_true (@prosa.behavior.schedule.scheduled_in Job
    (@prosa.model.processor.restricted_supply.rs_processor_state Job) j s) <->
  is_true (@prosa.model.processor.restricted_supply.rs_scheduled_on Job j s).
Proof.
  split.
  - rewrite /prosa.behavior.schedule.scheduled_in.
    move/existsP=> [c H]. by destruct c.
  - move=> H. rewrite /prosa.behavior.schedule.scheduled_in.
    apply/existsP. by exists tt.
Qed.

Lemma rss_source_bool_iff_eq (a b : bool) :
  (is_true a <-> is_true b) -> a = b.
Proof.
  destruct a, b; simpl; intros H; try reflexivity.
  - exfalso. discriminate (proj1 H (Logic.eq_refl true)).
  - exfalso. discriminate (proj2 H (Logic.eq_refl true)).
Qed.

Lemma rss_source_scheduled_in_concrete (Job : eqType) (j : Job)
    (s : @prosa.model.processor.restricted_supply.processor_state Job) :
  @prosa.behavior.schedule.scheduled_in Job
    (@prosa.model.processor.restricted_supply.rs_processor_state Job) j s =
  @prosa.model.processor.restricted_supply.rs_scheduled_on Job j s.
Proof.
  apply rss_source_bool_iff_eq.
  exact (rss_source_scheduled_in_iff_on Job j s).
Qed.

Local Lemma rss_sum_unit1 : forall {F : unit -> nat}, \sum_r F r = F tt.
Proof.
  move=> F.
  rewrite /index_enum unlock_with -enumT /=.
  have -> : enum (unit : finType) = [:: tt]
    by rewrite /(enum _) unlock //=.
  by rewrite big_seq1.
Qed.

Lemma rss_source_supply_in_concrete (Job : eqType)
    (s : @prosa.model.processor.restricted_supply.processor_state Job) :
  @prosa.behavior.schedule.supply_in Job
    (@prosa.model.processor.restricted_supply.rs_processor_state Job) s =
  @prosa.model.processor.restricted_supply.rs_supply_on Job s.
Proof.
  rewrite /prosa.behavior.schedule.supply_in /prosa.behavior.schedule.supply_on.
  exact rss_sum_unit1.
Qed.

Lemma rss_source_service_in_concrete (Job : eqType) (j : Job)
    (s : @prosa.model.processor.restricted_supply.processor_state Job) :
  @prosa.behavior.schedule.service_in Job
    (@prosa.model.processor.restricted_supply.rs_processor_state Job) j s =
  @prosa.model.processor.restricted_supply.rs_service_on Job j s.
Proof.
  rewrite /prosa.behavior.schedule.service_in /prosa.behavior.schedule.service_on.
  exact rss_sum_unit1.
Qed.

Print Assumptions rss_source_scheduled_in_concrete.
Print Assumptions rss_source_supply_in_concrete.
Print Assumptions rss_source_service_in_concrete.
