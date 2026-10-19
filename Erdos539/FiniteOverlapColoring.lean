/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionAffineTests

namespace Erdos539Geometry
noncomputable section
open scoped Classical
local instance reflectionColorIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

/-- A finite family with closed overlap neighborhoods of size at most k
has a k-coloring whose equal-color members are disjoint. -/
theorem finite_overlap_coloring {α β : Type*} (D : Finset α) (A : α → Finset β) (k : ℕ)
    (hA : ∀ x ∈ D, (A x).Nonempty)
    (hk : ∀ x ∈ D, (D.filter (fun y ↦ ¬Disjoint (A x) (A y))).card ≤ k) :
    ∃ c : α → ℕ, (∀ x ∈ D, c x < k) ∧
      ∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y → Disjoint (A x) (A y) := by
  induction D using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ 0, by simp, by simp⟩
  | @insert x D hx ih =>
    have hsub : D ⊆ insert x D := Finset.subset_insert _ _
    obtain ⟨c, hc, hdisj⟩ := ih (fun y hy ↦ hA y (hsub hy)) (by
      intro y hy
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hk y (hsub hy)))
    let N := D.filter (fun y ↦ ¬Disjoint (A x) (A y))
    have hself : ¬Disjoint (A x) (A x) := by
      obtain ⟨a, ha⟩ := hA x (Finset.mem_insert_self _ _)
      exact Finset.not_disjoint_iff.mpr ⟨a, ha, ha⟩
    have hN : N.card < k := by
      have hh := hk x (Finset.mem_insert_self _ _)
      rw [Finset.filter_insert, if_pos hself, Finset.card_insert_of_notMem] at hh
      · exact Nat.lt_of_succ_le hh
      · exact fun hn ↦ hx (Finset.mem_filter.mp hn).1
    have hcolors : (N.image c).card < (Finset.range k).card := by
      rw [Finset.card_range]
      exact Finset.card_image_le.trans_lt hN
    obtain ⟨a, ha, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcolors
    refine ⟨Function.update c x a, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa using Finset.mem_range.mp ha
      · rw [Function.update_of_ne (show y ≠ x by intro he; subst y; exact hx hy)]
        exact hc y hy
    · intro y hy z hz hyz he
      by_cases hyx : y = x
      · subst y
        have hzx : z ≠ x := Ne.symm hyz
        have hzD := (Finset.mem_insert.mp hz).resolve_left hzx
        rw [Function.update_self, Function.update_of_ne hzx] at he
        by_contra hd
        apply hnot
        exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzD, hd⟩, he.symm⟩
      · by_cases hzx : z = x
        · subst z
          have hyD := (Finset.mem_insert.mp hy).resolve_left hyx
          rw [Function.update_of_ne hyx, Function.update_self] at he
          by_contra hd
          apply hnot
          exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyD, fun h ↦ hd h.symm⟩, he⟩
        · rw [Function.update_of_ne hyx, Function.update_of_ne hzx] at he
          exact hdisj y ((Finset.mem_insert.mp hy).resolve_left hyx)
            z ((Finset.mem_insert.mp hz).resolve_left hzx) hyz he

theorem reflectionTest_sixteen_coloring (D : Finset ℤ) (w z : ℤ) :
    ∃ c : ℤ → ℕ, (∀ x ∈ D, c x < 16) ∧
      ∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y →
        Disjoint (reflectionTestSites w z x) (reflectionTestSites w z y) := by
  apply finite_overlap_coloring D (reflectionTestSites w z) 16
  · intro x _
    exact ⟨reflectionTestSite w z x 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  · intro x _
    exact reflectionTest_overlap_card_le D w z x

end
end Erdos539Geometry
