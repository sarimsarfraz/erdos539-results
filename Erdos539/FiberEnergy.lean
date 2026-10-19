/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductEnergy
import Erdos539.EnergySupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

theorem weightedEnergy_le_norm_squareSum (S : Finset G) (w : G → ℝ) :
    weightedEnergy S w ≤ energyNorm S * weightSquareSum S w ^ 2 := by
  have he : weightedEnergy S w = weightedEnergy S (extendWeight S (fun x ↦ w x)) := by
    apply weightedEnergy_congr
    intro x hx
    simp only [extendWeight, dif_pos hx]
  have hsq : weightSquareSum S w = ∑ x : S, w x ^ 2 := by
    unfold weightSquareSum
    rw [← Finset.sum_attach S]
    rfl
  rw [he, hsq]
  exact energyNorm_bound S (fun x ↦ w x)

theorem weightedEnergy_le_support_norm {A U : Finset G} (hAU : A ⊆ U) (w : G → ℝ)
    (hzero : ∀ x ∈ U, x ∉ A → w x = 0) :
    weightedEnergy U w ≤ energyNorm A * weightSquareSum U w ^ 2 := by
  rw [← weightedEnergy_support hAU w hzero, ← weightSquareSum_support hAU w hzero]
  exact weightedEnergy_le_norm_squareSum A w

def rowSupport (S : Finset (G × H)) (v : H) : Finset G :=
  (S.filter (fun p ↦ p.2 = v)).image Prod.fst

omit [AddCommGroup G] [AddCommGroup H] in
@[simp] theorem mem_rowSupport {S : Finset (G × H)} {u : G} {v : H} :
    u ∈ rowSupport S v ↔ (u, v) ∈ S := by
  simp only [rowSupport, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨hab, hb⟩, ha⟩
    subst a
    subst b
    exact hab
  · intro huv
    exact ⟨u, v, ⟨huv, rfl⟩, rfl⟩

omit [AddCommGroup G] [AddCommGroup H] in
theorem rowSupport_subset {S : Finset (G × H)} {U : Finset G} {V : Finset H}
    (hS : S ⊆ U ×ˢ V) (v : H) : rowSupport S v ⊆ U := by
  intro u hu
  exact (Finset.mem_product.mp (hS (mem_rowSupport.mp hu))).1

omit [AddCommGroup G] [AddCommGroup H] in
def rowNormWeight (U : Finset G) (w : G × H → ℝ) (v : H) : ℝ :=
  Real.sqrt (weightSquareSum U (fun u ↦ w (u,v)))

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem rowNormWeight_nonneg (U : Finset G) (w : G × H → ℝ) (v : H) : 0 ≤ rowNormWeight U w v :=
  Real.sqrt_nonneg _

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem rowNormWeight_pow_four (U : Finset G) (w : G × H → ℝ) (v : H) :
    rowNormWeight U w v ^ 4 = weightSquareSum U (fun u ↦ w (u,v)) ^ 2 := by
  unfold rowNormWeight
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (weightSquareSum_nonneg _ _)]

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem rowNormWeight_mono (U : Finset G) {w w' : G × H → ℝ} (v : H)
    (hw : ∀ u ∈ U, 0 ≤ w (u,v)) (hle : ∀ u ∈ U, w (u,v) ≤ w' (u,v)) :
    rowNormWeight U w v ≤ rowNormWeight U w' v := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro u hu
  exact pow_le_pow_left₀ (hw u hu) (hle u hu) 2

/-- The fiber estimate for an arbitrary relation inside an arbitrary finite
rectangle. The marginal is the actual square-root sum of squared weights. -/
theorem weightedEnergy_relation_le_marginal {S : Finset (G × H)} {U : Finset G} {V : Finset H}
    (hS : S ⊆ U ×ˢ V) (w : G × H → ℝ)
    (hzero : ∀ p ∈ U ×ˢ V, p ∉ S → w p = 0) {M : ℝ} (hM : 0 ≤ M)
    (hrows : ∀ v ∈ V, energyNorm (rowSupport S v) ≤ M) :
    weightedEnergy S w ≤ M * weightedEnergy V (rowNormWeight U w) := by
  rw [weightedEnergy_support hS w hzero]
  apply weightedEnergy_product_le_marginal U V w (rowNormWeight U w) hM
    (fun v _ ↦ rowNormWeight_nonneg U w v)
  intro v hv
  have hz : ∀ u ∈ U, u ∉ rowSupport S v → w (u,v) = 0 := by
    intro u hu hun
    exact hzero (u,v) (Finset.mem_product.mpr ⟨hu, hv⟩) (fun hs ↦ hun (mem_rowSupport.mpr hs))
  have hb := weightedEnergy_le_support_norm (rowSupport_subset hS v) (fun u ↦ w (u,v)) hz
  rw [rowNormWeight_pow_four]
  exact hb.trans (mul_le_mul_of_nonneg_right (hrows v hv) (sq_nonneg _))

end
end Erdos539Geometry
