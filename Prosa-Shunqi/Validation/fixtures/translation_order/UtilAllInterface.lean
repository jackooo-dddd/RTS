import Prosa.Util.All

/-!
Kernel-elaborated interface probes for the zero-declaration aggregation module
`Prosa.Util.All`.  This file deliberately imports only the aggregator.  Each
probe therefore checks that one authoritative direct dependency remains
observable through the compiled aggregation artifact.
-/

#check Prosa.Util.Notation.constant
#check Prosa.Util.Bigcat.bigCatFin
#check Prosa.Util.Bigop.bigSeq
#check Prosa.Util.Div_mod.eqdivn_leqmodn
#check Prosa.Util.List.max0
#check Prosa.Util.Nat.subnACA
#check Prosa.Util.Sum.sumSeq
#check Prosa.Util.Seqset.set
#check Prosa.Util.UnitGrowth.unit_growth_function
#check Prosa.Util.SearchArg.search_arg
#check Prosa.Util.Rel.monotone
#check Prosa.Util.Minmax.bigMaxListCond
#check Prosa.Util.Supremum.supremum
#check Prosa.Util.Nondecreasing.distances
#check Prosa.Util.Setoid.leb
#check Prosa.Util.Tactics.neqP
#check Prosa.Util.Poet.forall_exists_implied_by_forall_in_zip

open Prosa.Util.Epsilon

/-- The source aggregation module re-exports the `epsilon` notation module.
This compiled probe observes that `ε` elaborates to the natural numeral one
when only `Prosa.Util.All` is imported. -/
def Prosa.Validation.UtilAllInterface.epsilonValue : Nat := ε

example : Prosa.Validation.UtilAllInterface.epsilonValue = 1 := rfl
