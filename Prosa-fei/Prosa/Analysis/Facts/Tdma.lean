-- Translated from: ../rt-proofs/analysis/facts/tdma.v
import Prosa.Model.Schedule.Tdma
import Prosa.Util.All

namespace Prosa.Analysis.Facts.Tdma

open Prosa.Model.Schedule.Tdma
open Prosa.Util.Seqset
open Prosa.Util.Rel
open Prosa.Behavior.Time

section TDMAFacts

  variable {Task : Type _} [DecidableEq Task]

  variable (ts : SeqSet Task)

  variable [TDMAPolicy Task]

  section TimeSlotFacts

    variable (task : Task)
    variable (H_task_in_ts : task ∈ ts)
    variable (time_slot_positive : valid_time_slot ts)

    include H_task_in_ts time_slot_positive in
    theorem TDMA_cycle_ge_each_time_slot :
      TDMA_cycle ts ≥ task_time_slot task := by
      unfold TDMA_cycle
      apply List.single_le_sum
      · intro y hy; exact Nat.zero_le _
      · exact List.mem_map_of_mem H_task_in_ts

    include H_task_in_ts time_slot_positive in
    theorem TDMA_cycle_positive :
      TDMA_cycle ts > 0 := by
      calc 0 < task_time_slot task := time_slot_positive task H_task_in_ts
        _ ≤ TDMA_cycle ts := TDMA_cycle_ge_each_time_slot ts task H_task_in_ts time_slot_positive

    include H_task_in_ts time_slot_positive in
    theorem Offset_add_slot_leq_cycle :
      task_slot_offset ts task + task_time_slot task ≤ TDMA_cycle ts := by
      unfold task_slot_offset TDMA_cycle
      -- Helper: for any list, filter.map.sum ≤ map.sum
      have filter_map_sum_le : ∀ (l : List Task) (q : Task → Bool),
          List.sum (List.map task_time_slot (List.filter q l)) ≤
          List.sum (List.map task_time_slot l) :=
        fun l q => List.Sublist.sum_le_sum
          (List.Sublist.map task_time_slot (List.filter_sublist (p := q)))
          (fun _ _ => Nat.zero_le _)
      -- Use induction to get the combined bound
      set l := ts._set_seq
      set p := fun prev_task => slot_order prev_task task && decide (prev_task ≠ task)
      suffices h : ∀ (l' : List Task), task ∈ l' →
          List.sum (List.map task_time_slot (List.filter p l')) +
          task_time_slot task ≤ List.sum (List.map task_time_slot l') from
        h l H_task_in_ts
      intro l' hmem
      induction l' with
      | nil => simp at hmem
      | cons hd tl ih =>
        simp only [List.map_cons, List.sum_cons, List.filter_cons]
        rcases List.mem_cons.mp hmem with rfl | htl
        · -- task = hd: p task = false since decide (task ≠ task) = false
          have hp : p task = false := by simp [p]
          simp [hp]
          -- Goal: filter.map.sum + task_time_slot task ≤ task_time_slot task + tl.map.sum
          have h := filter_map_sum_le tl p
          calc (List.map task_time_slot (List.filter p tl)).sum + task_time_slot task
              = task_time_slot task + (List.map task_time_slot (List.filter p tl)).sum := by ring
            _ ≤ task_time_slot task + (List.map task_time_slot tl).sum :=
              Nat.add_le_add_left h _
        · -- task ∈ tl: use IH
          specialize ih htl
          split
          · -- p hd = true: filter adds hd
            simp only [List.map_cons, List.sum_cons]
            calc (task_time_slot hd + (List.map task_time_slot (List.filter p tl)).sum) + task_time_slot task
                = task_time_slot hd + ((List.map task_time_slot (List.filter p tl)).sum + task_time_slot task) := by ring
              _ ≤ task_time_slot hd + (List.map task_time_slot tl).sum := Nat.add_le_add_left ih _
          · -- p hd = false: filter skips hd
            calc (List.map task_time_slot (List.filter p tl)).sum + task_time_slot task
                ≤ (List.map task_time_slot tl).sum := ih
              _ ≤ task_time_slot hd + (List.map task_time_slot tl).sum := Nat.le_add_left _ _

    include H_task_in_ts time_slot_positive in
    theorem Offset_lt_cycle :
      task_slot_offset ts task < TDMA_cycle ts := by
      have h2 := time_slot_positive task H_task_in_ts
      calc task_slot_offset ts task
          < task_slot_offset ts task + task_time_slot task := Nat.lt_add_of_pos_right h2
        _ ≤ TDMA_cycle ts := Offset_add_slot_leq_cycle ts task H_task_in_ts time_slot_positive

  end TimeSlotFacts

  section TimeSlotOrderFacts

    variable (task : Task)
    variable (H_task_in_ts : task ∈ ts)
    variable (time_slot_positive : valid_time_slot ts)
    variable (slot_order_total : total_slot_order ts)
    variable (slot_order_antisymmetric : antisymmetric_slot_order ts)
    variable (slot_order_transitive : transitive_slot_order (Task := Task))

    include slot_order_antisymmetric slot_order_transitive in
    theorem relation_offset :
      ∀ tsk1 tsk2, tsk1 ∈ ts →
        tsk2 ∈ ts →
        slot_order tsk1 tsk2 = true →
        tsk1 ≠ tsk2 →
        task_slot_offset ts tsk2 ≥
          task_slot_offset ts tsk1 + task_time_slot tsk1 := by
      intro tsk1 tsk2 IN1 IN2 ORDER NEQ
      simp only [task_slot_offset]
      -- Name the filter predicates to enable simp matching
      set p1 := fun prev_task => slot_order prev_task tsk1 && decide (prev_task ≠ tsk1) with hp1_def
      set p2 := fun prev_task => slot_order prev_task tsk2 && decide (prev_task ≠ tsk2) with hp2_def
      -- Predicate implication: p1 hd → p2 hd
      have h_pred_imp : ∀ (hd : Task), p1 hd = true → p2 hd = true := by
        intro hd hpx
        simp only [hp1_def, Bool.and_eq_true, decide_eq_true_eq] at hpx
        simp only [hp2_def, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨slot_order_transitive hd tsk1 tsk2 hpx.1 ORDER,
               fun heq => NEQ (slot_order_antisymmetric tsk1 tsk2 IN1 IN2 ORDER (heq ▸ hpx.1))⟩
      -- p1(tsk1) = false, p2(tsk1) = true
      have hp1_val : p1 tsk1 = false := by simp [hp1_def]
      have hp2_val : p2 tsk1 = true := by simp [hp2_def, ORDER, NEQ]
      -- Filter monotonicity: filter p1 <+ filter p2
      have filter_mono : ∀ (l : List Task), (l.filter p1).Sublist (l.filter p2) := by
        intro l
        induction l with
        | nil => exact List.nil_sublist _
        | cons hd tl ih =>
          simp only [List.filter_cons]
          split_ifs with h1 h2
          · exact ih.cons₂ _
          · exact absurd (h_pred_imp _ h1) h2
          · exact ih.cons _
          · exact ih
      -- Main inequality by induction
      suffices hsuff : ∀ (l : List Task), l.Nodup → tsk1 ∈ l →
          ((l.filter p1).map task_time_slot).sum + task_time_slot tsk1 ≤
          ((l.filter p2).map task_time_slot).sum by
        exact hsuff ts._set_seq ts.set_seq_uniq IN1
      intro l hnd hmem
      induction l with
      | nil => simp at hmem
      | cons hd tl ih =>
        rw [List.nodup_cons] at hnd
        rcases List.mem_cons.mp hmem with rfl | htl
        · -- hd = tsk1: p1 tsk1 = false, p2 tsk1 = true
          have hf1 : List.filter p1 (tsk1 :: tl) = List.filter p1 tl := by simp [hp1_val]
          have hf2 : List.filter p2 (tsk1 :: tl) = tsk1 :: List.filter p2 tl := by simp [hp2_val]
          rw [hf1, hf2, List.map_cons, List.sum_cons]
          have hsub := List.Sublist.sum_le_sum
            (List.Sublist.map task_time_slot (filter_mono tl))
            (fun _ _ => Nat.zero_le _)
          rw [Nat.add_comm]
          exact Nat.add_le_add_left hsub _
        · -- tsk1 ∈ tl: use IH
          specialize ih hnd.2 htl
          cases h1 : p1 hd <;> cases h2 : p2 hd
          · -- p1 false, p2 false
            have hf1 : List.filter p1 (hd :: tl) = List.filter p1 tl := by simp [h1]
            have hf2 : List.filter p2 (hd :: tl) = List.filter p2 tl := by simp [h2]
            rw [hf1, hf2]; exact ih
          · -- p1 false, p2 true
            have hf1 : List.filter p1 (hd :: tl) = List.filter p1 tl := by simp [h1]
            have hf2 : List.filter p2 (hd :: tl) = hd :: List.filter p2 tl := by simp [h2]
            rw [hf1, hf2, List.map_cons, List.sum_cons]
            exact le_trans ih (Nat.le_add_left _ _)
          · -- p1 true, p2 false: contradiction with h_pred_imp
            exact absurd h2 (by simp [h_pred_imp hd h1])
          · -- p1 true, p2 true
            have hf1 : List.filter p1 (hd :: tl) = hd :: List.filter p1 tl := by simp [h1]
            have hf2 : List.filter p2 (hd :: tl) = hd :: List.filter p2 tl := by simp [h2]
            rw [hf1, hf2, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
            rw [Nat.add_assoc]
            exact Nat.add_le_add_left ih _

    include time_slot_positive slot_order_total slot_order_antisymmetric slot_order_transitive in
    theorem task_in_time_slot_uniq :
      ∀ tsk1 tsk2 t, tsk1 ∈ ts → task_time_slot tsk1 > 0 →
        tsk2 ∈ ts → task_time_slot tsk2 > 0 →
        task_in_time_slot ts tsk1 t →
        task_in_time_slot ts tsk2 t →
        tsk1 = tsk2 := by
      -- Core arithmetic lemma: non-overlapping intervals can't contain the same point
      have key : ∀ (cycle o1 o2 s1 s2 tm : ℕ),
          o1 < cycle → o2 < cycle → cycle > 0 →
          o1 + s1 ≤ cycle → o2 + s2 ≤ cycle →
          o2 ≥ o1 + s1 →
          tm < cycle →
          (if tm ≥ o1 then tm - o1 else tm + cycle - o1) < s1 →
          (if tm ≥ o2 then tm - o2 else tm + cycle - o2) < s2 →
          False := by
        intro cycle o1 o2 s1 s2 tm hCO1 hCO2 _ hSO1 hSO2 hrel htm G1 G2
        rcases Nat.lt_or_ge tm o1 with h1 | h1
        · simp only [if_neg (show ¬(tm ≥ o1) by omega)] at G1
          rcases Nat.lt_or_ge tm o2 with h2 | h2
          · simp only [if_neg (show ¬(tm ≥ o2) by omega)] at G2; omega
          · omega
        · simp only [if_pos h1] at G1
          simp only [if_neg (show ¬(tm ≥ o2) by omega)] at G2
          omega
      intro tsk1 tsk2 t IN1 SLOT1 IN2 SLOT2
      unfold task_in_time_slot
      set cycle := TDMA_cycle ts
      set o1 := task_slot_offset ts tsk1
      set o2 := task_slot_offset ts tsk2
      have hC : cycle > 0 := TDMA_cycle_positive ts tsk1 IN1 time_slot_positive
      have hSO1 : o1 + task_time_slot tsk1 ≤ cycle :=
        Offset_add_slot_leq_cycle ts tsk1 IN1 time_slot_positive
      have hSO2 : o2 + task_time_slot tsk2 ≤ cycle :=
        Offset_add_slot_leq_cycle ts tsk2 IN2 time_slot_positive
      have hCO1 : o1 < cycle := Offset_lt_cycle ts tsk1 IN1 time_slot_positive
      have hCO2 : o2 < cycle := Offset_lt_cycle ts tsk2 IN2 time_slot_positive
      simp only [Nat.mod_eq_of_lt hCO1, Nat.mod_eq_of_lt hCO2]
      rw [Prosa.Util.Div_mod.mod_elim t o1 cycle hC hCO1]
      rw [Prosa.Util.Div_mod.mod_elim t o2 cycle hC hCO2]
      have htm_lt : t % cycle < cycle := Nat.mod_lt t hC
      intro G1 G2
      by_contra NEQ
      rcases slot_order_total tsk1 tsk2 IN1 IN2 with hord | hord
      · have hord' : slot_order tsk1 tsk2 = true := hord
        have hrel := @relation_offset _ _ ts _ slot_order_antisymmetric slot_order_transitive
            tsk1 tsk2 IN1 IN2 hord' NEQ
        exact key cycle o1 o2 _ _ (t % cycle) hCO1 hCO2 hC hSO1 hSO2 hrel htm_lt G1 G2
      · have hord' : slot_order tsk2 tsk1 = true := hord
        have hrel := @relation_offset _ _ ts _ slot_order_antisymmetric slot_order_transitive
            tsk2 tsk1 IN2 IN1 hord' (Ne.symm NEQ)
        exact key cycle o2 o1 _ _ (t % cycle) hCO2 hCO1 hC hSO2 hSO1 hrel htm_lt G2 G1

  end TimeSlotOrderFacts

end TDMAFacts

end Prosa.Analysis.Facts.Tdma
