/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.DyadicRegularization

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

/-- Dyadic regularization followed by relative projection balance yields two
complementary coordinate blocks with small projection sizes. -/
theorem exists_regularized_partition {F : Finset (ι → ℝ)} (hF : F.Nonempty)
    (hd : 0 < Fintype.card ι) {N : ℕ} (hFN : F.card ≤ N) :
    ∃ S ⊆ F, S.Nonempty ∧
      F.card ≤ dyadicLevels N ^ (2 ^ Fintype.card ι - 2) * S.card ∧
      ∃ I J : Finset ι, (∀ i, i ∈ I ∨ i ∈ J) ∧ I.card + J.card = Fintype.card ι ∧
        (projection S I).card ≤ 2 ^ (Fintype.card ι + 3) *
          dyadicLevels N ^ (2 ^ Fintype.card ι - 2) * maxFan F ∧
        (projection S J).card ≤ 2 ^ (Fintype.card ι + 3) *
          dyadicLevels N ^ (2 ^ Fintype.card ι - 2) * maxFan F := by
  classical
  obtain ⟨S, hSF, hS, hsize, hregular⟩ := exists_dyadic_regularization hF hd hFN
  let B := dyadicLevels N ^ (2 ^ Fintype.card ι - 2)
  obtain ⟨I, _, hI, hJ⟩ := relative_projection_balance (Finset.Subset.refl S) hS ∅
    (2 * B * S.card) hregular
  rw [Finset.empty_union] at hI
  rw [Finset.empty_union, Finset.sdiff_empty] at hJ
  simp only [Finset.sdiff_empty, Finset.card_univ,
    maxRestrictedFan_empty, projection_empty_card hS, mul_one] at hI hJ
  have hbal (K : Finset ι)
      (hK : S.card * (projection S K).card ≤
        4 * 2 ^ Fintype.card ι * (2 * B * S.card) * maxFan S) :
      (projection S K).card ≤ 2 ^ (Fintype.card ι + 3) * B * maxFan F := by
    have hc : S.card * (projection S K).card ≤
        S.card * (2 ^ (Fintype.card ι + 3) * B * maxFan S) := by
      calc
        _ ≤ _ := hK
        _ = _ := by rw [pow_add]; norm_num; ring
    have hc' := Nat.le_of_mul_le_mul_left hc hS.card_pos
    exact hc'.trans (Nat.mul_le_mul_left _ (maxFan_mono hSF))
  refine ⟨S, hSF, hS, hsize, I, Finset.univ \ I, ?_, ?_, hbal I hI,
    hbal (Finset.univ \ I) hJ⟩
  · intro i
    by_cases hi : i ∈ I
    · exact Or.inl hi
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
  · have h := Finset.card_sdiff_of_subset (Finset.subset_univ I)
    have hi := Finset.card_le_univ I
    simp only [Finset.card_univ] at h
    omega

end
end Erdos539Geometry
