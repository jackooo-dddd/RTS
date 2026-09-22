import Validation.fixtures.translation_order.SupplyComputationInterface

#eval IO.println "FREEZE_BEGIN Prosa.Model.Processor.Supply.supply_at"
#check @Prosa.Model.Processor.Supply.supply_at
#eval IO.println "FREEZE_END Prosa.Model.Processor.Supply.supply_at"
#print axioms Prosa.Model.Processor.Supply.supply_at

#eval IO.println "FREEZE_BEGIN Prosa.Model.Processor.Supply.supply_during"
#check @Prosa.Model.Processor.Supply.supply_during
#eval IO.println "FREEZE_END Prosa.Model.Processor.Supply.supply_during"
#print axioms Prosa.Model.Processor.Supply.supply_during

#eval IO.println "FREEZE_BEGIN Prosa.Model.Processor.Supply.has_supply"
#check @Prosa.Model.Processor.Supply.has_supply
#eval IO.println "FREEZE_END Prosa.Model.Processor.Supply.has_supply"
#print axioms Prosa.Model.Processor.Supply.has_supply

#eval IO.println "FREEZE_BEGIN Prosa.Model.Processor.Supply.is_blackout"
#check @Prosa.Model.Processor.Supply.is_blackout
#eval IO.println "FREEZE_END Prosa.Model.Processor.Supply.is_blackout"
#print axioms Prosa.Model.Processor.Supply.is_blackout

#eval IO.println "FREEZE_BEGIN Prosa.Model.Processor.Supply.blackout_during"
#check @Prosa.Model.Processor.Supply.blackout_during
#eval IO.println "FREEZE_END Prosa.Model.Processor.Supply.blackout_during"
#print axioms Prosa.Model.Processor.Supply.blackout_during

#check @Prosa.Validation.ScheduleInterface.coreEnumeration
#print axioms Prosa.Validation.ScheduleInterface.coreEnumeration
#check @Prosa.Validation.ScheduleInterface.production_supply_in_as_list_sum
#print axioms Prosa.Validation.ScheduleInterface.production_supply_in_as_list_sum

#check @Prosa.Validation.SupplyInterface.supplyAtProjection
#print axioms Prosa.Validation.SupplyInterface.supplyAtProjection
#check @Prosa.Validation.SupplyInterface.supplyDuringProjection
#print axioms Prosa.Validation.SupplyInterface.supplyDuringProjection
#check @Prosa.Validation.SupplyInterface.hasSupplyProjection
#print axioms Prosa.Validation.SupplyInterface.hasSupplyProjection
#check @Prosa.Validation.SupplyInterface.isBlackoutProjection
#print axioms Prosa.Validation.SupplyInterface.isBlackoutProjection
#check @Prosa.Validation.SupplyInterface.blackoutDuringProjection
#print axioms Prosa.Validation.SupplyInterface.blackoutDuringProjection

#check @Prosa.Validation.SupplyInterface.supplyAtProjection_guard
#print axioms Prosa.Validation.SupplyInterface.supplyAtProjection_guard
#check @Prosa.Validation.SupplyInterface.supplyDuringProjection_guard
#print axioms Prosa.Validation.SupplyInterface.supplyDuringProjection_guard
#check @Prosa.Validation.SupplyInterface.hasSupplyProjection_guard
#print axioms Prosa.Validation.SupplyInterface.hasSupplyProjection_guard
#check @Prosa.Validation.SupplyInterface.isBlackoutProjection_guard
#print axioms Prosa.Validation.SupplyInterface.isBlackoutProjection_guard
#check @Prosa.Validation.SupplyInterface.blackoutDuringProjection_guard
#print axioms Prosa.Validation.SupplyInterface.blackoutDuringProjection_guard
