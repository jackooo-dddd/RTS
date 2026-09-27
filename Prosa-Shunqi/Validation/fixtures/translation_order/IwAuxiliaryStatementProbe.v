Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IwAuxiliarySemanticSource.
Import IwAuxiliarySemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.fold_cumul_interference". Abort.
Print statement_fold_cumul_interference.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.fold_cumul_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_alt". Abort.
Print statement_cumul_cond_interference_alt.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_alt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_sub". Abort.
Print statement_cumulative_interference_sub.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_sub". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_cat". Abort.
Print statement_cumulative_interference_cat.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_ID". Abort.
Print statement_cumul_cond_interference_ID.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_ID". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_pred_eq". Abort.
Print statement_cumul_cond_interference_pred_eq.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_pred_eq". Abort.
