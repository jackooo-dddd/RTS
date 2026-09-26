Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TransformPrefixSemanticSource.
Import TransformPrefixSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.transform.prefix.prefix_map". Abort.
Check @prefix_map.
Goal True. idtac "END|prosa.analysis.transform.prefix.prefix_map". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.prefix.prefix_map_property_invariance". Abort.
Print statement_prefix_map_property_invariance.
Goal True. idtac "END|prosa.analysis.transform.prefix.prefix_map_property_invariance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.prefix.prefix_map_pointwise_property". Abort.
Print statement_prefix_map_pointwise_property.
Goal True. idtac "END|prosa.analysis.transform.prefix.prefix_map_pointwise_property". Abort.
