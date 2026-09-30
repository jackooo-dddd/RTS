import Prosa.Analysis.Abstract.Ideal.IwInstantiation
import Validation.fixtures.translation_order.RsIwInstantiationComputationInterface
import Validation.fixtures.translation_order.IdealInstWitnessComputationInterface
import Validation.fixtures.translation_order.IdealScheduleComputationInterface

/-!
Export root for `analysis/abstract/ideal/iw_instantiation.v`: the twenty statements (statement-only), together with
the accepted restricted-supply iw-instantiation export root, the validation-only ideal universe witnesses (so that the
generic processor-state-dependent constants used by the replayed certificate helpers appear at the ideal processor
universe instance) and the accepted ideal-schedule root (its accepted closed-form ideal-state equations). No new
equation is added.
-/
