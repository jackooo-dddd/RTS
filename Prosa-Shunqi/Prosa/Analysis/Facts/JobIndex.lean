-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/job_index.v

import Prosa.Analysis.Facts.Model.TaskArrivals

namespace Prosa.Analysis.Facts.JobIndex

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Util.Bigcat
open Prosa.Util.List
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.TaskArrivals

/-- `omega'` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-! Representation notes: MathComp's `index x s` is `List.idxOf x s`, `x \in s`
in Prop position is `decide (x ∈ s) = true`, `nth x0 s n` is `s.getD n x0`,
`s = [::]` is `s = []`, `j1 <> j2` is `j1 ≠ j2`. -/

section JobIndexLemmas

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]

private theorem mem_up_to (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) (j : Job) (h : arrives_in arr_seq j) :
    j ∈ task_arrivals_up_to_job_arrival (Task := Task) arr_seq j :=
  of_decide_eq_true (arrives_in_task_arrivals_up_to arr_seq hva.1 j h)

theorem case_arrival_lte_implies_equal_job (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = job_task (Task := Task) j2 →
        job_index (Task := Task) arr_seq j1 = job_index (Task := Task) arr_seq j2 →
        job_arrival j1 ≤ job_arrival j2 → j1 = j2 := by
  intro hva j1 j2 h1 h2 htsk hidx hle
  obtain ⟨xs, hcat⟩ := task_arrivals_up_to_prefix_cat (Task := Task) arr_seq j1 j2 h1 h2 htsk hle
  have m1 := mem_up_to (Task := Task) arr_seq hva j1 h1
  have m2 := mem_up_to (Task := Task) arr_seq hva j2 h2
  unfold job_index at hidx
  rw [← hcat] at hidx
  rw [← List.idxOf_append_of_mem (l₂ := xs) m1] at hidx
  exact (List.idxOf_inj (List.mem_append_left _ m1)).mp hidx

theorem case_arrival_gt_implies_equal_job (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = job_task (Task := Task) j2 →
        job_index (Task := Task) arr_seq j1 = job_index (Task := Task) arr_seq j2 →
        job_arrival j2 < job_arrival j1 → j1 = j2 := by
  intro hva j1 j2 h1 h2 htsk hidx hlt
  exact (case_arrival_lte_implies_equal_job (Task := Task) arr_seq hva j2 j1 h2 h1 htsk.symm
    hidx.symm (Nat.le_of_lt hlt)).symm

theorem equal_index_implies_equal_jobs (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = job_task (Task := Task) j2 →
        job_index (Task := Task) arr_seq j1 = job_index (Task := Task) arr_seq j2 → j1 = j2 := by
  intro hva j1 j2 h1 h2 htsk hidx
  by_cases hle : job_arrival j1 ≤ job_arrival j2
  · exact case_arrival_lte_implies_equal_job arr_seq hva j1 j2 h1 h2 htsk hidx hle
  · exact case_arrival_gt_implies_equal_job arr_seq hva j1 j2 h1 h2 htsk hidx (by omega')

theorem diff_jobs_iff_diff_indices (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = job_task (Task := Task) j2 →
        (j1 ≠ j2 ↔ job_index (Task := Task) arr_seq j1 ≠ job_index (Task := Task) arr_seq j2) := by
  intro hva j1 j2 h1 h2 htsk
  constructor
  · intro hne heq; exact hne (equal_index_implies_equal_jobs arr_seq hva j1 j2 h1 h2 htsk heq)
  · intro hne heq; subst heq; exact hne rfl

theorem index_as_sum_size_and_index (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 : Job, arrives_in arr_seq j1 →
        job_index (Task := Task) arr_seq j1 =
          (task_arrivals_before_job_arrival (Task := Task) arr_seq j1).length +
            (task_arrivals_at_job_arrival (Task := Task) arr_seq j1).idxOf j1 := by
  intro hva j1 h1
  unfold job_index
  rw [task_arrivals_up_to_cat (Task := Task) arr_seq j1 h1]
  apply List.idxOf_append_of_notMem
  intro hin
  unfold task_arrivals_before_job_arrival task_arrivals_before task_arrivals_between at hin
  have hin' := (List.mem_filter.mp hin).1
  have := job_arrival_between arr_seq hva.1 j1 0 (job_arrival j1) (decide_eq_true hin')
  simp at this

end JobIndexLemmas

section ArrivalsBetweenP

variable {Job : JobType} [DecidableEq Job] [JobArrival Job]

theorem arrival_lt_implies_job_in_arrivals_between_P (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (j1 j2 : Job) (P : Job → Bool) (t1 t2 : instant),
        decide (j1 ∈ arrivals_between_P arr_seq P t1 t2) = true →
        decide (j2 ∈ arrivals_between_P arr_seq P t1 t2) = true →
        job_arrival j2 < job_arrival j1 →
        decide (j2 ∈ arrivals_between_P arr_seq P t1 (job_arrival j1)) = true := by
  intro hva j1 j2 P t1 t2 _ hin2 hlt
  have hb := job_arrival_between_P arr_seq hva.1 j2 P t1 t2 hin2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have hm := List.mem_filter.mp (of_decide_eq_true hin2)
  apply decide_eq_true
  refine List.mem_filter.mpr ⟨?_, hm.2⟩
  have harr : arrives_in arr_seq j2 := in_arrivals_implies_arrived arr_seq j2 t1 t2 (decide_eq_true hm.1)
  exact of_decide_eq_true (job_in_arrivals_between arr_seq hva.1 j2 t1 (job_arrival j1) harr hb.1 hlt)

theorem index_lte_implies_arrival_lte_P (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (j1 j2 : Job) (P : Job → Bool) (t1 t2 : instant),
        decide (j1 ∈ arrivals_between_P arr_seq P t1 t2) = true →
        decide (j2 ∈ arrivals_between_P arr_seq P t1 t2) = true →
        (arrivals_between_P arr_seq P t1 t2).idxOf j1 ≤ (arrivals_between_P arr_seq P t1 t2).idxOf j2 →
        job_arrival j1 ≤ job_arrival j2 := by
  intro hva j1 j2 P t1 t2 hin1 hin2 hle
  by_contra hgt
  have hlt : job_arrival j2 < job_arrival j1 := by omega'
  have hb1 := job_arrival_between_P arr_seq hva.1 j1 P t1 t2 hin1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb1
  have hcat := arrivals_P_cat arr_seq P (job_arrival j1) t1 t2 (by simp [hb1.1, hb1.2])
  have hj2 := of_decide_eq_true (arrival_lt_implies_job_in_arrivals_between_P arr_seq hva j1 j2 P t1 t2 hin1 hin2 hlt)
  have hj1 : j1 ∉ arrivals_between_P arr_seq P t1 (job_arrival j1) := by
    intro h
    have := job_arrival_between_P arr_seq hva.1 j1 P t1 (job_arrival j1) (decide_eq_true h)
    simp at this
  rw [hcat, List.idxOf_append_of_mem hj2, List.idxOf_append_of_notMem hj1] at hle
  have := (List.idxOf_lt_length_iff).mpr hj2
  omega'

end ArrivalsBetweenP

section JobIndexLemmas2

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]

theorem job_index_same_in_task_arrivals (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = job_task (Task := Task) j2 →
        job_arrival j1 ≤ job_arrival j2 →
        (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1).idxOf j1 =
          (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j2).idxOf j1 := by
  intro hva j1 j2 h1 h2 htsk hle
  obtain ⟨xs, hcat⟩ := task_arrivals_up_to_prefix_cat (Task := Task) arr_seq j1 j2 h1 h2 htsk hle
  rw [← hcat, List.idxOf_append_of_mem (mem_up_to (Task := Task) arr_seq hva j1 h1)]

theorem index_job_lt_size_task_arrivals_up_to_job (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 : Job, arrives_in arr_seq j1 →
        job_index (Task := Task) arr_seq j1 <
          (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1).length := by
  intro hva j1 h1
  exact List.idxOf_lt_length_iff.mpr (mem_up_to (Task := Task) arr_seq hva j1 h1)

theorem index_lte_implies_arrival_lte (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = job_task (Task := Task) j2 →
        job_index (Task := Task) arr_seq j2 ≤ job_index (Task := Task) arr_seq j1 →
        job_arrival j2 ≤ job_arrival j1 := by
  intro hva j1 j2 h1 h2 htsk hle
  by_contra hgt
  have hlt : job_arrival j1 < job_arrival j2 := by omega'
  obtain ⟨xs, hne, hcat⟩ := arrival_lt_implies_strict_prefix (Task := Task) arr_seq hva.1
    (job_task (Task := Task) j2) j1 j2 htsk rfl h1 h2 hlt
  unfold job_index at hle
  have m1 := mem_up_to (Task := Task) arr_seq hva j1 h1
  have m2 := mem_up_to (Task := Task) arr_seq hva j2 h2
  -- j2 is not among the jobs up to j1's arrival
  have hn2 : j2 ∉ task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1 := by
    intro h
    have hm := (List.mem_filter.mp h).1
    have := job_arrival_between arr_seq hva.1 j2 0 (job_arrival j1 + 1) (decide_eq_true hm)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    omega'
  rw [← hcat, List.idxOf_append_of_notMem hn2] at hle
  have := List.idxOf_lt_length_iff.mpr m1
  omega'

theorem earlier_arrival_implies_lower_index (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = job_task (Task := Task) j2 →
        job_arrival j1 < job_arrival j2 →
        job_index (Task := Task) arr_seq j1 < job_index (Task := Task) arr_seq j2 := by
  intro hva j1 j2 h1 h2 htsk hlt
  by_contra hge
  have := index_lte_implies_arrival_lte (Task := Task) arr_seq hva j1 j2 h1 h2 htsk (by omega')
  omega'

theorem job_index_minus_one_lt_size_task_arrivals_up_to (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 : Job, arrives_in arr_seq j1 →
        job_index (Task := Task) arr_seq j1 - 1 <
          (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1).length := by
  intro hva j1 h1
  have := index_job_lt_size_task_arrivals_up_to_job (Task := Task) arr_seq hva j1 h1
  omega'

theorem positive_job_index_implies_positive_size_of_task_arrivals (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j1 : Job, arrives_in arr_seq j1 →
        0 < (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1).length := by
  intro hva j1 h1
  exact List.length_pos_of_mem (mem_up_to (Task := Task) arr_seq hva j1 h1)

end JobIndexLemmas2

/-! ## Previous job -/

section PreviousJob

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]

theorem prev_job_arr (arr_seq : arrival_sequence Job) (j : Job) :
    arrives_in arr_seq j → arrives_in arr_seq (prev_job (Task := Task) arr_seq j) := by
  intro h
  unfold prev_job
  by_cases hlt : job_index (Task := Task) arr_seq j - 1 <
      (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).length
  · rw [List.getD_eq_getElem _ _ hlt]
    have hm := List.getElem_mem hlt
    exact in_arrivals_implies_arrived arr_seq _ 0 (job_arrival j + 1)
      (decide_eq_true (List.mem_filter.mp hm).1)
  · rw [List.getD_eq_default _ _ (by omega')]
    exact h

private theorem prev_job_eq_getElem (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) (j : Job) (h : arrives_in arr_seq j) :
    ∃ hlt : job_index (Task := Task) arr_seq j - 1 <
        (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).length,
      prev_job (Task := Task) arr_seq j =
        (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j)[job_index (Task := Task) arr_seq j - 1] :=
  ⟨job_index_minus_one_lt_size_task_arrivals_up_to arr_seq hva j h,
    List.getD_eq_getElem _ _ _⟩

private theorem nodup_up_to (arr_seq : arrival_sequence Job) (hva : valid_arrival_sequence arr_seq)
    (j : Job) : (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).Nodup :=
  uniq_task_arrivals arr_seq hva.1 _ _ hva.2

theorem prev_job_index (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j : Job, arrives_in arr_seq j → 0 < job_index (Task := Task) arr_seq j →
        (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).idxOf (prev_job (Task := Task) arr_seq j) =
          job_index (Task := Task) arr_seq j - 1 := by
  intro hva j h _
  obtain ⟨hlt, heq⟩ := prev_job_eq_getElem (Task := Task) arr_seq hva j h
  rw [heq]
  exact List.Nodup.idxOf_getElem (nodup_up_to arr_seq hva j) _ hlt

theorem prev_job_in_task_arrivals_up_to_j (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j : Job, arrives_in arr_seq j →
        decide (prev_job (Task := Task) arr_seq j ∈ task_arrivals_up_to_job_arrival (Task := Task) arr_seq j) = true := by
  intro hva j h
  obtain ⟨hlt, heq⟩ := prev_job_eq_getElem (Task := Task) arr_seq hva j h
  rw [heq]
  exact decide_eq_true (List.getElem_mem hlt)

theorem prev_job_task (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j : Job, arrives_in arr_seq j → 0 < job_index (Task := Task) arr_seq j →
        job_task (Task := Task) (prev_job (Task := Task) arr_seq j) = job_task (Task := Task) j := by
  intro hva j h _
  have hm := of_decide_eq_true (prev_job_in_task_arrivals_up_to_j (Task := Task) arr_seq hva j h)
  have := (List.mem_filter.mp hm).2
  simpa [job_of_task] using this

theorem prev_job_arr_lte (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j : Job, arrives_in arr_seq j → 0 < job_index (Task := Task) arr_seq j →
        job_arrival (prev_job (Task := Task) arr_seq j) ≤ job_arrival j := by
  intro hva j h _
  have hm := of_decide_eq_true (prev_job_in_task_arrivals_up_to_j (Task := Task) arr_seq hva j h)
  have := job_arrival_between arr_seq hva.1 _ 0 (job_arrival j + 1)
    (decide_eq_true (List.mem_filter.mp hm).1)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega'

theorem prev_job_index_j (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j : Job, arrives_in arr_seq j → 0 < job_index (Task := Task) arr_seq j →
        0 < job_index (Task := Task) arr_seq j →
        job_index (Task := Task) arr_seq (prev_job (Task := Task) arr_seq j) =
          job_index (Task := Task) arr_seq j - 1 := by
  intro hva j h hpos _
  rw [← prev_job_index (Task := Task) arr_seq hva j h hpos]
  exact job_index_same_in_task_arrivals (Task := Task) arr_seq hva _ j
    (prev_job_arr (Task := Task) arr_seq j h) h (prev_job_task arr_seq hva j h hpos)
    (prev_job_arr_lte arr_seq hva j h hpos)

theorem no_jobs_between_consecutive_jobs (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j : Job, arrives_in arr_seq j → 0 < job_index (Task := Task) arr_seq j →
        0 < job_index (Task := Task) arr_seq j →
        task_arrivals_between arr_seq (job_task (Task := Task) j)
          (job_arrival (prev_job (Task := Task) arr_seq j) + 1) (job_arrival j) = [] := by
  intro hva j h hpos _
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro j3 hin
  have hm := List.mem_filter.mp hin
  have htsk : job_task (Task := Task) j3 = job_task (Task := Task) j := by simpa [job_of_task] using hm.2
  have harr3 : arrives_in arr_seq j3 := in_arrivals_implies_arrived arr_seq j3 _ _ (decide_eq_true hm.1)
  have hb := job_arrival_between arr_seq hva.1 j3 _ _ (decide_eq_true hm.1)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have hp := prev_job_arr (Task := Task) arr_seq j h
  have hpt := prev_job_task (Task := Task) arr_seq hva j h hpos
  have hi1 := earlier_arrival_implies_lower_index (Task := Task) arr_seq hva _ j3 hp harr3
    (by rw [hpt, htsk]) (by omega')
  have hi2 := earlier_arrival_implies_lower_index (Task := Task) arr_seq hva j3 j harr3 h htsk hb.2
  rw [prev_job_index_j (Task := Task) arr_seq hva j h hpos hpos] at hi1
  omega'

theorem exists_jobs_before_j (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ j : Job, arrives_in arr_seq j →
        ∀ k : Nat, k < job_index (Task := Task) arr_seq j →
          ∃ j' : Job, j ≠ j' ∧ job_task (Task := Task) j' = job_task (Task := Task) j ∧
            arrives_in arr_seq j' ∧ job_index (Task := Task) arr_seq j' = k := by
  intro hva j h k hk
  have hsize := index_job_lt_size_task_arrivals_up_to_job (Task := Task) arr_seq hva j h
  have hkl : k < (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).length := by omega'
  set jk := (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j)[k] with hjk
  have hin : jk ∈ task_arrivals_up_to_job_arrival (Task := Task) arr_seq j := List.getElem_mem hkl
  have hm := List.mem_filter.mp hin
  have htsk : job_task (Task := Task) jk = job_task (Task := Task) j := by simpa [job_of_task] using hm.2
  have harr : arrives_in arr_seq jk := in_arrivals_implies_arrived arr_seq jk _ _ (decide_eq_true hm.1)
  have hb := job_arrival_between arr_seq hva.1 jk _ _ (decide_eq_true hm.1)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have hidx : (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).idxOf jk = k :=
    List.Nodup.idxOf_getElem (nodup_up_to arr_seq hva j) _ hkl
  have hji : job_index (Task := Task) arr_seq jk = k := by
    unfold job_index
    rw [job_index_same_in_task_arrivals (Task := Task) arr_seq hva jk j harr h htsk (by omega'), hidx]
  refine ⟨jk, ?_, htsk, harr, hji⟩
  intro heq
  rw [← heq] at hji
  omega'

end PreviousJob

end Prosa.Analysis.Facts.JobIndex
