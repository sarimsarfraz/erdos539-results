/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerSelection

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- On coordinates minimized by an actual anchor, its forward fan determines
the entire coordinate projection. -/
theorem projection_card_le_fan_of_minimum (S : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ)
    (hmin : ∀ x ∈ S, ∀ i ∈ I, a i ≤ x i) : (projection S I).card ≤ (fan S a).card := by
  let f : (ι → ℝ) → (I → ℝ) := fun z i ↦ z i + a i
  have he : (fan S a).image f = projection S I := by
    rw [fan, Finset.image_image]
    apply Finset.image_congr
    intro x hx
    funext i
    dsimp only [f, pdiff, project, Function.comp_apply]
    rw [max_eq_left (sub_nonneg.mpr (hmin x hx i i.property))]
    ring
  rw [← he]
  exact Finset.card_image_le

variable [Fintype ι]

/-- A large two-corner slice has both complementary projection supports
controlled by forward fans at its two actual corners. -/
theorem exists_corner_partition {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (hd : 0 < Fintype.card ι) :
    ∃ E ⊆ S, E.Nonempty ∧
      S.card ≤ 2 ^ (3 * 2 ^ (Fintype.card ι - 1) + 5) * E.card ∧
      ∃ I J : Finset ι, (∀ i, i ∈ I ∨ i ∈ J) ∧ I.card + J.card = Fintype.card ι ∧
        (projection E I).card ≤ maxFan S ∧ (projection E J).card ≤ maxFan S := by
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hd
  obtain ⟨a, ha, b, hb, hsize⟩ := exists_large_corner_slice hS i
  let E := cornerSlice S a b
  let I := Finset.univ.filter (fun i ↦ a i ≤ b i)
  let J := Finset.univ \ I
  have haE : a ∈ E := mem_cornerSlice.mpr ⟨ha, inCornerBox_left a b⟩
  have hbE : b ∈ E := mem_cornerSlice.mpr ⟨hb, inCornerBox_right a b⟩
  have hES : E ⊆ S := cornerSlice_subset S a b
  refine ⟨E, hES, ⟨a, haE⟩, hsize, I, J, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ I
    · exact Or.inl hj
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
  · have h := Finset.card_sdiff_of_subset (Finset.subset_univ I)
    have hi := Finset.card_le_univ I
    dsimp only [J]
    simp only [Finset.card_univ] at h
    omega
  · have hp := projection_card_le_fan_of_minimum E I a (by
      intro x hx j hj
      have hbox := (mem_cornerSlice.mp hx).2 j
      have hj' := (Finset.mem_filter.mp hj).2
      simpa only [min_eq_left hj'] using hbox.1)
    exact hp.trans ((card_fan_le_maxFan haE).trans (maxFan_mono hES))
  · have hp := projection_card_le_fan_of_minimum E J b (by
      intro x hx j hj
      have hbox := (mem_cornerSlice.mp hx).2 j
      have hn := (Finset.mem_sdiff.mp hj).2
      have hba : b j ≤ a j := by
        by_contra h
        have hab : a j ≤ b j := (lt_of_not_ge h).le
        exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
      simpa only [min_eq_right hba] using hbox.1)
    exact hp.trans ((card_fan_le_maxFan hbE).trans (maxFan_mono hES))

end
end Erdos539Geometry
