/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyNormalization

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem weightedEnergy_congr (S : Finset G) {f g : G → ℝ} (hfg : ∀ x ∈ S, f x = g x) :
    weightedEnergy S f = weightedEnergy S g := by
  unfold weightedEnergy
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp (mem_fiber.mp hp).1
  rw [hfg _ ha, hfg _ hb]

omit [AddCommGroup G] [DecidableEq G] in
theorem weightSquareSum_support {A S : Finset G} (hAS : A ⊆ S) (f : G → ℝ)
    (hzero : ∀ x ∈ S, x ∉ A → f x = 0) : weightSquareSum A f = weightSquareSum S f := by
  apply Finset.sum_subset hAS
  intro x hx hxa
  rw [hzero x hx hxa, zero_pow (by decide : 2 ≠ 0)]

omit [AddCommGroup G] [DecidableEq G] in
theorem pair_weight_zero_of_not_mem {A S : Finset G} (f : G → ℝ)
    (hzero : ∀ x ∈ S, x ∉ A → f x = 0) {p : G × G}
    (hp : p ∈ S ×ˢ S) (hpa : p ∉ A ×ˢ A) : f p.1 * f p.2 = 0 := by
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  by_cases hxa : p.1 ∈ A
  · have hya : p.2 ∉ A := fun h ↦ hpa (Finset.mem_product.mpr ⟨hxa, h⟩)
    rw [hzero _ hy hya, mul_zero]
  · rw [hzero _ hx hxa, zero_mul]

/-- Adding zero-weight points to the supplied ambient support leaves the
literal additive energy unchanged. -/
theorem weightedEnergy_support {A S : Finset G} (hAS : A ⊆ S) (f : G → ℝ)
    (hzero : ∀ x ∈ S, x ∉ A → f x = 0) : weightedEnergy A f = weightedEnergy S f := by
  rw [weightedEnergy_eq_quadruples, weightedEnergy_eq_quadruples]
  have hp : A ×ˢ A ⊆ S ×ˢ S := Finset.product_subset_product hAS hAS
  calc
    _ = ∑ p ∈ A ×ˢ A, ∑ q ∈ S ×ˢ S,
        if p.1 + p.2 = q.1 + q.2 then (f p.1 * f p.2) * (f q.1 * f q.2) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_subset hp
      intro q hq hqa
      rw [pair_weight_zero_of_not_mem f hzero hq hqa, mul_zero]
      simp
    _ = _ := by
      apply Finset.sum_subset hp
      intro p hp' hpa
      rw [pair_weight_zero_of_not_mem f hzero hp' hpa]
      simp

omit [AddCommGroup G] in
theorem extendWeight_zero_of_not_mem (S : Finset G) (f : S → ℝ) {x : G} (hx : x ∉ S) :
    extendWeight S f x = 0 := by simp only [extendWeight, dif_neg hx]

omit [AddCommGroup G] in
theorem extendWeight_lift {A S : Finset G} (hAS : A ⊆ S) (f : A → ℝ) :
    extendWeight S (fun x ↦ extendWeight A f x) = extendWeight A f := by
  funext x
  by_cases hx : x ∈ S
  · simp only [extendWeight, dif_pos hx]
  · have hxa : x ∉ A := fun h ↦ hx (hAS h)
    simp only [extendWeight, dif_neg hx, dif_neg hxa]

/-- The actual energy norm is monotone on subsets, by zero extension of
an exact maximizing weight. -/
theorem energyNorm_mono {A S : Finset G} (hAS : A ⊆ S) : energyNorm A ≤ energyNorm S := by
  by_cases hA : A.Nonempty
  · obtain ⟨f, hf, hnorm, hE⟩ := energyNorm_attained hA
    let g : S → ℝ := fun x ↦ extendWeight A f x
    have hzero : ∀ x ∈ S, x ∉ A → extendWeight A f x = 0 := fun _ _ hx ↦ extendWeight_zero_of_not_mem A f hx
    have hg : g ∈ admissibleWeights S := by
      refine ⟨?_, ?_⟩
      · intro x
        change 0 ≤ extendWeight A f x
        by_cases hx : x.val ∈ A
        · simpa only [extendWeight, dif_pos hx] using hf ⟨x, hx⟩
        · rw [extendWeight_zero_of_not_mem A f hx]
      · rw [← weightSquareSum_extend, extendWeight_lift hAS,
          ← weightSquareSum_support hAS _ hzero, weightSquareSum_extend]
        exact hnorm
    have h := energyNorm_ge_admissible hg
    rw [extendWeight_lift hAS, ← weightedEnergy_support hAS _ hzero, hE] at h
    exact h
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA, energyNorm_empty]
    exact energyNorm_nonneg S

end
end Erdos539Geometry
