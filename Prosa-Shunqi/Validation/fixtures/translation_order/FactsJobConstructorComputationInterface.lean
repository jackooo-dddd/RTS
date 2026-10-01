import Prosa.Implementation.Facts.JobConstructor
import Validation.fixtures.translation_order.JobConstructorComputationInterface

/-!
Export root for `implementation/facts/job_constructor.v`: the six statements (statement-only), together with the
accepted job-constructor definitions export root.

Three equations are added: the accepted `BigcatInterface` equations of the half-open big concatenation, instantiated at
the concrete job type. `arrivals_between` over concrete jobs is the concrete (universe-0) copy of `bigCat`, which the
generic equations do not mention; each equation is proved by the accepted generic one.
-/

namespace Prosa.Validation.FactsJobConstructorInterface

open Prosa.Util.Notation
open Prosa.Implementation.Definitions.Task

theorem production_bigCat_job_same (m : Nat) (f : Nat → List concrete_job) :
    bigCat m m f = [] :=
  Prosa.Validation.BigcatInterface.production_bigCat_same m f

theorem production_bigCat_job_of_le (m n : Nat) (f : Nat → List concrete_job) (h : n ≤ m) :
    bigCat m n f = [] :=
  Prosa.Validation.BigcatInterface.production_bigCat_of_le m n f h

theorem production_bigCat_job_add_succ (m d : Nat) (f : Nat → List concrete_job) :
    bigCat m (m + (d + 1)) f = bigCat m (m + d) f ++ f (m + d) :=
  Prosa.Validation.BigcatInterface.production_bigCat_add_succ m d f

end Prosa.Validation.FactsJobConstructorInterface
