import Prosa.Analysis.Facts.Transform.EdfOpt
import Validation.fixtures.translation_order.EdfDefinitionsComputationInterface
import Validation.fixtures.translation_order.FactsEdfTransComputationInterface

/-!
Export root for `analysis/facts/transform/edf_opt.v`: the 43 statements (statement-only), together with the
accepted edf-definitions export root (ideal processor, EDF_at / EDF_schedule, schedulability, basic readiness,
identical_prefix) merged with the accepted edf-trans export root (the six transformation definitions, search_arg,
prefix_map, swapped and their accepted kernel-checked equations). No new equation is added.
-/
