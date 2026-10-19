/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GluingPositiveEncoding

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

/-- Every encoded regime is realized by actual pairs of gluing points. -/
theorem positiveGlueEncode_mem {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)}
    (hFn : F.Nonempty) (hGn : G.Nonempty) {K : ℕ} (hK : 0 < K)
    {M : ℤ} (hM : 0 < M) (hF : HasCoordinateGap F M) (hG : HasCoordinateGap G M)
    {p : GluePositiveIndex ι κ} (hp : p ∈ positiveGlueIndices F G K) :
    positiveGlueEncode M p ∈ integerPositiveDifferences (gluing F G K M) := by
  rcases p with p | (p | p)
  all_goals simp only [positiveGlueIndices, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
    Finset.mem_product, Finset.mem_Ico] at hp
  · obtain ⟨x, hx, x', hx', hxx⟩ := mem_integerPositiveDifferences.mp hp.1
    obtain ⟨y, hy, y', hy', hyy⟩ := mem_integerPositiveDifferences.mp hp.2
    apply mem_integerPositiveDifferences.mpr
    refine ⟨glueVector M 0 x y, mem_gluing.mpr ⟨0, hK, x, hx, y, hy, rfl⟩,
      glueVector M 0 x' y', mem_gluing.mpr ⟨0, hK, x', hx', y', hy', rfl⟩, ?_⟩
    rw [intPdiff_glueVector_same, hxx, hyy]
    rfl
  · obtain ⟨x, hx, x', hx', hxx⟩ := mem_integerDifferences.mp hp.2
    obtain ⟨y, hy⟩ := hGn
    have hcast : (p.1.toNat : ℤ) = p.1 := by omega
    have hlt : p.1.toNat < K := by omega
    apply mem_integerPositiveDifferences.mpr
    refine ⟨glueVector M p.1.toNat x y, mem_gluing.mpr ⟨p.1.toNat, hlt, x, hx, y, hy, rfl⟩,
      glueVector M 0 x' y, mem_gluing.mpr ⟨0, hK, x', hx', y, hy, rfl⟩, ?_⟩
    rw [intPdiff_glueVector_of_gt hM hF hG (by omega) hx hx' hy hy, hcast, sub_zero, hxx]
    rfl
  · obtain ⟨y, hy, y', hy', hyy⟩ := mem_integerDifferences.mp hp.2
    obtain ⟨x, hx⟩ := hFn
    have hcast : (p.1.toNat : ℤ) = p.1 := by omega
    have hlt : p.1.toNat < K := by omega
    apply mem_integerPositiveDifferences.mpr
    refine ⟨glueVector M 0 x y, mem_gluing.mpr ⟨0, hK, x, hx, y, hy, rfl⟩,
      glueVector M p.1.toNat x y', mem_gluing.mpr ⟨p.1.toNat, hlt, x, hx, y', hy', rfl⟩, ?_⟩
    rw [intPdiff_glueVector_of_lt hM hF hG (by omega) hx hx hy hy', hcast, sub_zero, hyy]
    rfl

/-- The exact positive-difference identity from the gluing proposition. Both
coordinate blocks are nonempty, as in the manuscript's positive-dimensional split. -/
theorem gluing_integerPositiveDifferences_card_eq {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)}
    (hFn : F.Nonempty) (hGn : G.Nonempty) {K : ℕ} (hK : 0 < K)
    {L M : ℤ} (hL : 0 ≤ L) (hM : 2 * L < M)
    (hF : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L)
    (hG : ∀ x ∈ G, ∀ y ∈ G, ∀ i, |x i - y i| ≤ L) (i : ι) (j : κ) :
    (integerPositiveDifferences (gluing F G K M)).card =
      (integerPositiveDifferences F).card * (integerPositiveDifferences G).card +
        (K - 1) * ((integerDifferences F).card + (integerDifferences G).card) := by
  have hMp : 0 < M := by omega
  have hf := coordinateGap_of_diameter hL hM hF
  have hg := coordinateGap_of_diameter hL hM hG
  apply Nat.le_antisymm (gluing_integerPositiveDifferences_card_le K hMp hf hg)
  rw [← positiveGlueIndices_card F G K]
  exact Finset.card_le_card_of_injOn (positiveGlueEncode M)
    (fun _ hp ↦ positiveGlueEncode_mem hFn hGn hK hMp hf hg hp)
    (positiveGlueEncode_injOn K hL hM hF hG i j)

end
end Erdos539Geometry
