Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.WcTransSemanticSource.
Import WcTransSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module WcTransProbeDisplay. Definition processor_state := tt. End WcTransProbeDisplay.
Import WcTransProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.relevant_pstate". Abort.
Check @relevant_pstate.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.relevant_pstate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.max_deadline_for_jobs_arrived_before". Abort.
Check @max_deadline_for_jobs_arrived_before.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.max_deadline_for_jobs_arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.find_swap_candidate". Abort.
Check @find_swap_candidate.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.find_swap_candidate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.make_wc_at". Abort.
Check @make_wc_at.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.make_wc_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.wc_transform_prefix". Abort.
Check @wc_transform_prefix.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.wc_transform_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.wc_transform". Abort.
Check @wc_transform.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.wc_transform". Abort.
