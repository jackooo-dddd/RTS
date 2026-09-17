-- Translated from: ../rt-proofs/util/counting.v
import Mathlib.Data.List.Count

namespace Prosa.Util.Counting

section Counting

lemma count_filter_fun {T : Type _} [DecidableEq T] (l : List T) (P : T -> Bool) :
    List.countP (fun x => P x) l = (List.filter P l).length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.countP_cons, List.filter_cons]; split <;> simp [ih]

end Counting

end Prosa.Util.Counting
