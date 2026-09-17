-- Translated from: ../rt-proofs/classic/model/policy_tdma.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time

open Prosa.Classic.Model.Time
open Prosa.Util.Seqset
open Prosa.Classic.Util.Seqset
open Prosa.Classic.Util.List

namespace Prosa.Classic.Model.Policy_tdma

section TDMA

  variable (Task : Type _)

  abbrev TDMA_slot := Task → Duration

  abbrev TDMA_slot_order := Task → Task → Bool

end TDMA

section PropertiesTDMA

  variable {Task : Type _} [DecidableEq Task]

  variable (ts : SeqSet Task)

  variable (slot_order : TDMA_slot_order Task)

  section Relation

    def slot_order_is_transitive : Prop :=
      ∀ x y z : Task, slot_order x y = true → slot_order y z = true → slot_order x z = true

    def slot_order_is_total_over_task_set : Prop :=
      total_over_list slot_order ts._set_seq

    def slot_order_is_antisymmetric_over_task_set : Prop :=
      antisymmetric_over_list slot_order ts._set_seq

  end Relation

  section TimeSlot

    variable (task : Task)
    variable (H_task_in_ts : task ∈ ts)

    variable (task_time_slot : TDMA_slot Task)

    def is_valid_time_slot : Prop :=
      task_time_slot task > 0

    def TDMA_cycle : ℕ :=
      (ts._set_seq.map task_time_slot).sum

    def Task_slot_offset : ℕ :=
      ((ts._set_seq.filter (fun prev_task => slot_order prev_task task && decide (prev_task ≠ task))).map task_time_slot).sum

    def Task_in_time_slot (t : Time) : Prop :=
      ((t + TDMA_cycle ts task_time_slot - Task_slot_offset ts slot_order task task_time_slot % TDMA_cycle ts task_time_slot) % TDMA_cycle ts task_time_slot) <
        task_time_slot task

    section BasicLemmas

      variable (time_slot_positive : is_valid_time_slot task task_time_slot)

      include H_task_in_ts

      theorem TDMA_cycle_ge_each_time_slot :
          TDMA_cycle ts task_time_slot ≥ task_time_slot task := by
        unfold TDMA_cycle
        have hmem : task ∈ ts._set_seq := H_task_in_ts
        exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map_of_mem hmem)

      include time_slot_positive

      theorem TDMA_cycle_positive :
          TDMA_cycle ts task_time_slot > 0 := by
        calc 0 < task_time_slot task := time_slot_positive
          _ ≤ TDMA_cycle ts task_time_slot :=
            TDMA_cycle_ge_each_time_slot ts task H_task_in_ts task_time_slot

      include time_slot_positive in
      include H_task_in_ts in
      theorem Offset_lt_cycle :
          Task_slot_offset ts slot_order task task_time_slot < TDMA_cycle ts task_time_slot := by
        unfold Task_slot_offset TDMA_cycle
        have hmem : task ∈ ts._set_seq := H_task_in_ts
        have hnodup : ts._set_seq.Nodup := ts.set_seq_uniq
        have hpos : task_time_slot task > 0 := time_slot_positive
        set l := ts._set_seq
        set P := fun prev_task => slot_order prev_task task && decide (prev_task ≠ task)
        have hle : ((l.filter P).map task_time_slot).sum + task_time_slot task ≤
            (l.map task_time_slot).sum := by
          have hsum_eq : ((l.filter P).map task_time_slot).sum + task_time_slot task =
              (((l.filter P) ++ [task]).map task_time_slot).sum := by
            rw [List.map_append, List.sum_append, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, Nat.add_zero]
          rw [hsum_eq]
          apply Prosa.Classic.Util.Sum.leq_sum_sub_uniq
          · rw [List.nodup_append]
            refine ⟨List.Nodup.filter _ hnodup, List.nodup_singleton _, ?_⟩
            intro a ha b hb
            rw [List.mem_singleton] at hb
            subst hb
            rw [List.mem_filter] at ha
            obtain ⟨hmem_a, hPa⟩ := ha
            rw [Bool.and_eq_true] at hPa
            have hne := hPa.2
            rw [decide_eq_true_eq] at hne
            exact hne
          · intro x hx
            rw [List.mem_append] at hx
            rcases hx with hfl | htask
            · exact List.mem_of_mem_filter hfl
            · rw [List.mem_singleton] at htask
              rw [htask]
              exact hmem
        exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos) hle

      omit time_slot_positive in
      theorem Offset_add_slot_leq_cycle :
          Task_slot_offset ts slot_order task task_time_slot + task_time_slot task ≤ TDMA_cycle ts task_time_slot := by
        unfold Task_slot_offset TDMA_cycle
        have hmem : task ∈ ts._set_seq := H_task_in_ts
        have hnodup : ts._set_seq.Nodup := ts.set_seq_uniq
        -- We need: sum(filtered by slot_order && ≠ task) + slot(task) ≤ sum(all)
        -- Strategy: show that the filtered elements plus task form a sublist
        -- Use leq_sum_sub_uniq: if r1 ⊆ r2 and r1 is nodup, sum r1 ≤ sum r2
        -- r1 = (filter (slot_order && ≠ task)) ++ [task], r2 = ts._set_seq
        set l := ts._set_seq
        set P := fun prev_task => slot_order prev_task task && decide (prev_task ≠ task)
        -- sum of filtered + slot(task) = sum of (filtered ++ [task])
        have hsum_eq : ((l.filter P).map task_time_slot).sum + task_time_slot task =
            (((l.filter P) ++ [task]).map task_time_slot).sum := by
          simp [List.map_append, List.sum_append]
        rw [hsum_eq]
        -- Now show (filter P l ++ [task]) is a sublist with nodup and subset
        apply Prosa.Classic.Util.Sum.leq_sum_sub_uniq
        · -- Nodup of (filter P l ++ [task])
          rw [List.nodup_append]
          exact ⟨List.Nodup.filter _ hnodup, List.nodup_singleton _,
            fun a ha b hb => by
              rw [List.mem_singleton] at hb
              subst hb
              rw [List.mem_filter] at ha
              simp [P] at ha
              exact ha.2.2⟩
        · -- Every element of (filter P l ++ [task]) is in l
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hfl | htask
          · exact List.mem_of_mem_filter hfl
          · rw [List.mem_singleton] at htask
            rw [htask]
            exact hmem

    end BasicLemmas

  end TimeSlot

  section InTimeSlotUniq

    variable (task_time_slot : TDMA_slot Task)

    variable (slot_order_total : slot_order_is_total_over_task_set ts slot_order)

    variable (slot_order_antisymmetric : slot_order_is_antisymmetric_over_task_set ts slot_order)

    variable (slot_order_transitive : slot_order_is_transitive slot_order)

    include slot_order_antisymmetric slot_order_transitive

    theorem relation_offset :
        ∀ tsk1 tsk2, tsk1 ∈ ts → tsk2 ∈ ts →
        slot_order tsk1 tsk2 = true → tsk1 ≠ tsk2 →
        Task_slot_offset ts slot_order tsk2 task_time_slot ≥
          Task_slot_offset ts slot_order tsk1 task_time_slot + task_time_slot tsk1 := by
      intro tsk1 tsk2 IN1 IN2 ORDER NEQ
      unfold Task_slot_offset
      set l := ts._set_seq
      set P1 := fun prev_task => slot_order prev_task tsk1 && decide (prev_task ≠ tsk1)
      set P2 := fun prev_task => slot_order prev_task tsk2 && decide (prev_task ≠ tsk2)
      have hnodup : l.Nodup := ts.set_seq_uniq
      -- Strategy: (l.filter P1 ++ [tsk1]) has nodup, is a subset of l.filter P2
      -- So sum(l.filter P1 ++ [tsk1]) ≤ sum(l.filter P2)
      -- And sum(l.filter P1 ++ [tsk1]) = sum(l.filter P1) + slot(tsk1)
      have hsum_eq : ((l.filter P1).map task_time_slot).sum + task_time_slot tsk1 =
          (((l.filter P1) ++ [tsk1]).map task_time_slot).sum := by
        simp [List.map_append, List.sum_append]
      rw [hsum_eq]
      apply Prosa.Classic.Util.Sum.leq_sum_sub_uniq
      · -- Nodup of (filter P1 l ++ [tsk1])
        rw [List.nodup_append]
        refine ⟨List.Nodup.filter _ hnodup, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb; subst hb
        rw [List.mem_filter] at ha
        simp [P1] at ha
        exact ha.2.2
      · -- Every element of (filter P1 l ++ [tsk1]) is in (filter P2 l)
        intro x hx
        rw [List.mem_append] at hx
        rw [List.mem_filter]
        rcases hx with hfl | htsk
        · -- x is in filter P1 l → x is in filter P2 l
          rw [List.mem_filter] at hfl
          have hxl := hfl.1
          have hP1 := hfl.2
          simp [P1] at hP1
          constructor
          · exact hxl
          · simp [P2]
            refine ⟨slot_order_transitive x tsk1 tsk2 hP1.1 ORDER, ?_⟩
            -- x ≠ tsk2: if x = tsk2, then slot_order tsk2 tsk1 = true
            -- together with slot_order tsk1 tsk2 = true and antisymmetry → tsk1 = tsk2, contradiction
            intro heq
            subst heq
            exact NEQ (slot_order_antisymmetric x tsk1 hxl IN1 hP1.1 ORDER).symm
        · -- x = tsk1 → x is in filter P2 l
          rw [List.mem_singleton] at htsk; subst htsk
          exact ⟨IN1, by simp [P2, ORDER, NEQ]⟩

    include slot_order_total

    theorem task_in_time_slot_uniq :
        ∀ tsk1 tsk2 t, tsk1 ∈ ts → task_time_slot tsk1 > 0 →
        tsk2 ∈ ts → task_time_slot tsk2 > 0 →
        Task_in_time_slot ts slot_order tsk1 task_time_slot t →
        Task_in_time_slot ts slot_order tsk2 task_time_slot t →
        tsk1 = tsk2 := by
      -- Core arithmetic lemma: given the intervals don't overlap, can't be in both at once
      have key : ∀ (cycle o1 o2 s1 s2 tm : ℕ),
          o1 < cycle → o2 < cycle → cycle > 0 →
          o1 + s1 ≤ cycle → o2 + s2 ≤ cycle →
          o2 ≥ o1 + s1 →
          tm < cycle →
          (if tm ≥ o1 then tm - o1 else tm + cycle - o1) < s1 →
          (if tm ≥ o2 then tm - o2 else tm + cycle - o2) < s2 →
          False := by
        intro cycle o1 o2 s1 s2 tm hCO1 hCO2 hC hSO1 hSO2 hrel htm G1 G2
        by_cases h1 : tm ≥ o1 <;> by_cases h2 : tm ≥ o2 <;> simp only [h1, h2, ↓reduceIte] at G1 G2 <;> omega
      intro tsk1 tsk2 t IN1 SLOT1 IN2 SLOT2
      unfold Task_in_time_slot
      set cycle := TDMA_cycle ts task_time_slot
      set o1 := Task_slot_offset ts slot_order tsk1 task_time_slot
      set o2 := Task_slot_offset ts slot_order tsk2 task_time_slot
      have hC : cycle > 0 := TDMA_cycle_positive ts tsk1 IN1 task_time_slot SLOT1
      have hSO1 : o1 + task_time_slot tsk1 ≤ cycle :=
        Offset_add_slot_leq_cycle ts slot_order tsk1 IN1 task_time_slot
      have hSO2 : o2 + task_time_slot tsk2 ≤ cycle :=
        Offset_add_slot_leq_cycle ts slot_order tsk2 IN2 task_time_slot
      -- Derive o < cycle from o + slot ≤ cycle and slot > 0 (avoiding incomplete Offset_lt_cycle)
      have hCO1 : o1 < cycle := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right SLOT1) hSO1
      have hCO2 : o2 < cycle := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right SLOT2) hSO2
      simp only [Nat.mod_eq_of_lt hCO1, Nat.mod_eq_of_lt hCO2]
      rw [Prosa.Util.Div_mod.mod_elim t o1 cycle hC hCO1]
      rw [Prosa.Util.Div_mod.mod_elim t o2 cycle hC hCO2]
      have htm_lt : t % cycle < cycle := Nat.mod_lt t hC
      intro G1 G2
      by_contra NEQ
      rcases slot_order_total tsk1 tsk2 IN1 IN2 with hord | hord
      · have hneq12 : tsk1 ≠ tsk2 := NEQ
        have hrel := relation_offset ts slot_order task_time_slot
              slot_order_antisymmetric slot_order_transitive
              tsk1 tsk2 IN1 IN2 hord hneq12
        exact key cycle o1 o2 _ _ (t % cycle) hCO1 hCO2 hC hSO1 hSO2 hrel htm_lt G1 G2
      · have hneq21 : tsk2 ≠ tsk1 := Ne.symm NEQ
        have hrel := relation_offset ts slot_order task_time_slot
              slot_order_antisymmetric slot_order_transitive
              tsk2 tsk1 IN2 IN1 hord hneq21
        exact key cycle o2 o1 _ _ (t % cycle) hCO2 hCO1 hC hSO2 hSO1 hrel htm_lt G2 G1

  end InTimeSlotUniq

end PropertiesTDMA

end Prosa.Classic.Model.Policy_tdma
