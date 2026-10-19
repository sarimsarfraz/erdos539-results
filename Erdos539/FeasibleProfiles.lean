/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProfileStack

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- Reverse compression represented by exact feasible branching profiles of
the original coordinate-prefix tree. No original label is used as a rank. -/
def feasibleProfiles : (d : ℕ) → Finset (Fin d → ℝ) → Finset (Fin d → ℕ)
  | 0, S => if S.Nonempty then {0} else ∅
  | d + 1, S => profileStack (prefixLabels S) (fun t ↦ feasibleProfiles d (prefixChild S t))

/-- Exact leaf-count identity for the feasible-profile downset. -/
theorem feasibleProfiles_card (d : ℕ) (S : Finset (Fin d → ℝ)) :
    (feasibleProfiles d S).card = S.card := by
  induction d with
  | zero =>
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hS
      have he : S = {x} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hx, fun _ _ ↦ Subsingleton.elim _ _⟩
      simp [feasibleProfiles, he]
    · simp [feasibleProfiles, Finset.not_nonempty_iff_eq_empty.mp hS]
  | succ d ih =>
    rw [feasibleProfiles, profileStack_card]
    simp_rw [ih]
    exact sum_prefixChild_card S

theorem feasibleProfiles_nonempty_iff {d : ℕ} {S : Finset (Fin d → ℝ)} :
    (feasibleProfiles d S).Nonempty ↔ S.Nonempty := by
  rw [← Finset.card_pos, feasibleProfiles_card, Finset.card_pos]

theorem feasibleProfiles_mono (d : ℕ) {A S : Finset (Fin d → ℝ)} (hAS : A ⊆ S) :
    feasibleProfiles d A ⊆ feasibleProfiles d S := by
  induction d with
  | zero =>
    by_cases hA : A.Nonempty
    · have hS := hA.mono hAS
      simp [feasibleProfiles, hA, hS]
    · simp [feasibleProfiles, hA]
  | succ d ih =>
    exact profileStack_mono (prefixLabels_mono hAS) (fun t _ ↦ ih (prefixChild_mono hAS t))

/-- Downward closure expresses that one may always keep fewer children at
any level, without changing the actual labels of any retained child. -/
theorem feasibleProfiles_downward (d : ℕ) (S : Finset (Fin d → ℝ))
    {a b : Fin d → ℕ} (hb : b ∈ feasibleProfiles d S) (hab : a ≤ b) :
    a ∈ feasibleProfiles d S := by
  induction d with
  | zero => simpa only [show a = b from Subsingleton.elim _ _] using hb
  | succ d ih =>
    apply mem_profileStack.mpr
    have hb' := mem_profileStack.mp hb
    have hsub : (prefixLabels S).filter (fun t ↦ Fin.tail b ∈ feasibleProfiles d (prefixChild S t)) ⊆
        (prefixLabels S).filter (fun t ↦ Fin.tail a ∈ feasibleProfiles d (prefixChild S t)) := by
      intro t ht
      obtain ⟨ht, hb⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨ht, ih (prefixChild S t) hb (fun i ↦ hab i.succ)⟩
    exact (lt_of_le_of_lt (hab 0) hb').trans_le (Finset.card_le_card hsub)

end
end Erdos539Geometry
