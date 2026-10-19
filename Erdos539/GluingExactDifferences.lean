/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Gluing

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

/-- Every level in the full difference interval is realized by two allowed levels. -/
theorem exists_gluing_level_difference {K : ℕ} {g : ℤ}
    (hg : g ∈ Finset.Icc (1 - (K : ℤ)) ((K : ℤ) - 1)) :
    ∃ t < K, ∃ s < K, (t : ℤ) - s = g := by
  have hh := Finset.mem_Icc.mp hg
  by_cases hn : 0 ≤ g
  · exact ⟨g.toNat, by omega, 0, by omega, by omega⟩
  · exact ⟨0, by omega, (-g).toNat, by omega, by omega⟩

/-- The exact ordinary-difference identity, with separation for the first
block difference set. This is the stronger identity behind the upper estimate. -/
theorem gluing_integerDifferences_card_eq {F : Finset (ι → ℤ)}
    (G : Finset (κ → ℤ)) (K : ℕ) {M : ℤ} (hM : 0 < M)
    (hgap : HasCoordinateGap (integerDifferences F) M) (i : ι) :
    (integerDifferences (gluing F G K M)).card =
      (2 * K - 1) * (integerDifferences F).card * (integerDifferences G).card := by
  classical
  apply Nat.le_antisymm (gluing_integerDifferences_card_le F G K M)
  let levels : Finset ℤ := Finset.Icc (1 - (K : ℤ)) ((K : ℤ) - 1)
  let T := (levels ×ˢ integerDifferences F) ×ˢ integerDifferences G
  let f := fun p : (ℤ × (ι → ℤ)) × (κ → ℤ) ↦ glueVector M p.1.1 p.1.2 p.2
  have hcard : T.card ≤ (integerDifferences (gluing F G K M)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      obtain ⟨hp', hv⟩ := Finset.mem_product.mp hp
      obtain ⟨hg, hu⟩ := Finset.mem_product.mp hp'
      obtain ⟨t, ht, s, hs, hts⟩ := exists_gluing_level_difference hg
      obtain ⟨x, hx, x', hx', hxx⟩ := mem_integerDifferences.mp hu
      obtain ⟨y, hy, y', hy', hyy⟩ := mem_integerDifferences.mp hv
      apply mem_integerDifferences.mpr
      refine ⟨glueVector M t x y, mem_gluing.mpr ⟨t, ht, x, hx, y, hy, rfl⟩,
        glueVector M s x' y', mem_gluing.mpr ⟨s, hs, x', hx', y', hy', rfl⟩, ?_⟩
      rw [glueVector_sub, hts, hxx, hyy]
    · intro p hp q hq hpq
      have hpF := (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2
      have hqF := (Finset.mem_product.mp (Finset.mem_product.mp hq).1).2
      obtain ⟨hg, hu, hv⟩ := glueVector_injective_of_gap hM hgap i hpF hqF hpq
      exact Prod.ext (Prod.ext hg hu) hv
  have hlevels : levels.card = 2 * K - 1 := by
    dsimp only [levels]
    rw [Int.card_Icc]
    omega
  simpa only [T, Finset.card_product, hlevels] using hcard

/-- A coordinate diameter bound gives the original separating gap. -/
theorem coordinateGap_of_diameter {F : Finset (ι → ℤ)} {L M : ℤ}
    (hL : 0 ≤ L) (hM : 2 * L < M)
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L) : HasCoordinateGap F M := by
  intro x hx y hy i
  exact (hdiam x hx y hy i).trans_lt (by omega)

/-- Difference coordinates have diameter at most twice the original diameter. -/
theorem differences_coordinateGap_of_diameter {F : Finset (ι → ℤ)} {L M : ℤ}
    (hM : 2 * L < M)
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L) :
    HasCoordinateGap (integerDifferences F) M := by
  intro u hu v hv i
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerDifferences.mp hu
  obtain ⟨x', hx', y', hy', rfl⟩ := mem_integerDifferences.mp hv
  have h1 := abs_le.mp (hdiam x hx y hy i)
  have h2 := abs_le.mp (hdiam x' hx' y' hy' i)
  change |(x i - y i) - (x' i - y' i)| < M
  apply abs_lt.mpr
  constructor <;> omega

/-- The manuscript's ordinary-difference formula under M>2L. -/
theorem gluing_integerDifferences_card_eq_of_diameter {F : Finset (ι → ℤ)}
    (G : Finset (κ → ℤ)) (K : ℕ) {L M : ℤ} (hL : 0 ≤ L) (hM : 2 * L < M)
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L) (i : ι) :
    (integerDifferences (gluing F G K M)).card =
      (2 * K - 1) * (integerDifferences F).card * (integerDifferences G).card :=
  gluing_integerDifferences_card_eq G K (by omega)
    (differences_coordinateGap_of_diameter hM hdiam) i

end
end Erdos539Geometry
