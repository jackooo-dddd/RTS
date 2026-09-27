Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IbfSupplySemanticSource.
Import IbfSupplySemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply.intra_interference". Abort.
Check @intra_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply.intra_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply.cumul_intra_interference". Abort.
Check @cumul_intra_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply.cumul_intra_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply.intra_interference_is_bounded_by". Abort.
Check @intra_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply.intra_interference_is_bounded_by". Abort.
