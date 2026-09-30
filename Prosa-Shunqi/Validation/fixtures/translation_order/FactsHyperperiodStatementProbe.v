Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsHyperperiodSemanticSource.
Import FactsHyperperiodSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Require Import prosa.analysis.definitions.infinite_jobs.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.hyperperiod_int_mult_of_any_task". Abort.
Print statement_hyperperiod_int_mult_of_any_task.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.hyperperiod_int_mult_of_any_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.valid_periods_imply_pos_hp". Abort.
Print statement_valid_periods_imply_pos_hp.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.valid_periods_imply_pos_hp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.corresponding_jobs_have_same_task". Abort.
Print statement_corresponding_jobs_have_same_task.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.corresponding_jobs_have_same_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.all_jobs_arrive_within_hyperperiod". Abort.
Print statement_all_jobs_arrive_within_hyperperiod.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.all_jobs_arrive_within_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.eq_size_hyp_lt". Abort.
Print statement_eq_size_hyp_lt.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.eq_size_hyp_lt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.eq_size_of_arrivals_in_hyperperiod". Abort.
Print statement_eq_size_of_arrivals_in_hyperperiod.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.eq_size_of_arrivals_in_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.job_in_hp_arrives_in_task_arrivals_up_to". Abort.
Print statement_job_in_hp_arrives_in_task_arrivals_up_to.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.job_in_hp_arrives_in_task_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.job_in_own_hp". Abort.
Print statement_job_in_own_hp.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.job_in_own_hp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.corr_job_in_task_arrivals_up_to". Abort.
Print statement_corr_job_in_task_arrivals_up_to.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.corr_job_in_task_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.corresponding_job_arrives". Abort.
Print statement_corresponding_job_arrives.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.corresponding_job_arrives". Abort.
