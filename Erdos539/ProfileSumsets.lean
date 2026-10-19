/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FeasibleProfiles
import Erdos539.ElementarySumsets

namespace Erdos539Geometry
noncomputable section
open scoped Finset Pointwise Classical

theorem prefixChild_add_subset {d : ℕ} (S T : Finset (Fin (d + 1) → ℝ)) (s t : ℝ) :
    prefixChild S s + prefixChild T t ⊆ prefixChild (S + T) (s + t) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  apply mem_prefixChild.mpr
  have he : (Fin.cons (s + t) (x + y) : Fin (d + 1) → ℝ) =
      (Fin.cons s x : Fin (d + 1) → ℝ) + (Fin.cons t y : Fin (d + 1) → ℝ) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  rw [he]
  exact Finset.mem_add.mpr ⟨Fin.cons s x, mem_prefixChild.mp hx,
    Fin.cons t y, mem_prefixChild.mp hy, rfl⟩

/-- The feasible-profile compression is subadditive at the set level. This
uses ordered-line sumset counting and retains actual labels in its children. -/
theorem feasibleProfiles_add_subset (d : ℕ) (S T : Finset (Fin d → ℝ)) :
    feasibleProfiles d S + feasibleProfiles d T ⊆ feasibleProfiles d (S + T) := by
  induction d with
  | zero =>
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x, hx⟩ := feasibleProfiles_nonempty_iff.mp ⟨a, ha⟩
    obtain ⟨y, hy⟩ := feasibleProfiles_nonempty_iff.mp ⟨b, hb⟩
    have hST : (S + T).Nonempty := ⟨x + y, Finset.mem_add.mpr ⟨x, hx, y, hy, rfl⟩⟩
    have he : a + b = 0 := Subsingleton.elim _ _
    simp [feasibleProfiles, hST, he]
  | succ d ih =>
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    let A := (prefixLabels S).filter (fun t ↦ Fin.tail a ∈ feasibleProfiles d (prefixChild S t))
    let B := (prefixLabels T).filter (fun t ↦ Fin.tail b ∈ feasibleProfiles d (prefixChild T t))
    have ha' : a 0 < A.card := mem_profileStack.mp ha
    have hb' : b 0 < B.card := mem_profileStack.mp hb
    have hA : A.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) ha')
    have hB : B.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hb')
    have hsub : A + B ⊆ (prefixLabels (S + T)).filter
        (fun t ↦ Fin.tail (a + b) ∈ feasibleProfiles d (prefixChild (S + T) t)) := by
      intro v hv
      obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_add.mp hv
      have has := (Finset.mem_filter.mp hs).2
      have hbt := (Finset.mem_filter.mp ht).2
      have hsum := ih (prefixChild S s) (prefixChild T t)
        (Finset.mem_add.mpr ⟨Fin.tail a, has, Fin.tail b, hbt, rfl⟩)
      have hprof : Fin.tail (a + b) ∈ feasibleProfiles d (prefixChild (S + T) (s + t)) :=
        feasibleProfiles_mono d (prefixChild_add_subset S T s t) hsum
      have hlabel : s + t ∈ prefixLabels (S + T) :=
        prefixChild_nonempty_iff.mp (feasibleProfiles_nonempty_iff.mp ⟨Fin.tail (a + b), hprof⟩)
      exact Finset.mem_filter.mpr ⟨hlabel, hprof⟩
    have hsumcard := real_sumset_card_lower hA hB
    have hcard := Finset.card_le_card hsub
    apply mem_profileStack.mpr
    change a 0 + b 0 < ((prefixLabels (S + T)).filter
      (fun t ↦ Fin.tail (a + b) ∈ feasibleProfiles d (prefixChild (S + T) t))).card
    omega

/-- Cardinality is preserved and sumsets do not grow under profile compression. -/
theorem feasibleProfiles_sum_card_le (d : ℕ) (S : Finset (Fin d → ℝ)) :
    (feasibleProfiles d S + feasibleProfiles d S).card ≤ (S + S).card := by
  have h := Finset.card_le_card (feasibleProfiles_add_subset d S S)
  rwa [feasibleProfiles_card] at h

end
end Erdos539Geometry
