import Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
import Validation.fixtures.translation_order.IbfSupplyTaskComputationInterface
import Validation.fixtures.translation_order.BusyIntervalServiceInversionComputationInterface
import Validation.fixtures.translation_order.FactsInterferenceComputationInterface

/-!
Export root for `analysis/abstract/restricted_supply/iw_instantiation.v`: the seventeen statements and the
section-local instances `rs_jlfp_interference` / `rs_jlfp_interfering_workload`, together with the accepted
IBF/supply_task export root, the accepted busy-interval service-inversion export root (classical busy
intervals, priority inversion, preemption facts, service inversion) and the accepted interference-facts export
root (interference definitions). No new equation is added.
-/
