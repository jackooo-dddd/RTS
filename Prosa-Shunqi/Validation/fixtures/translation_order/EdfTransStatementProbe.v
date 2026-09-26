Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.EdfTransSemanticSource.
Import EdfTransSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module EdfTransProbeDisplay. Definition processor_state := tt. End EdfTransProbeDisplay.
Import EdfTransProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.earlier_deadline". Abort.
Check @earlier_deadline.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.earlier_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.relevant_pstate". Abort.
Check @relevant_pstate.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.relevant_pstate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.find_swap_candidate". Abort.
Check @find_swap_candidate.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.find_swap_candidate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.make_edf_at". Abort.
Check @make_edf_at.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.make_edf_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.edf_transform_prefix". Abort.
Check @edf_transform_prefix.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.edf_transform_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.edf_transform". Abort.
Check @edf_transform.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.edf_transform". Abort.
