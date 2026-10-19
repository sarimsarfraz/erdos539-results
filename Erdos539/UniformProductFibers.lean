/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SidonUniformOptimizer
import Erdos539.ReflectedCountingProducts
import Erdos539.GibbsImageFibers

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem first_product_fiber {S : Finset G} (T : Finset H) {a : G} (ha : a ∈ S) :
    fiber (S ×ˢ T) Prod.fst a = {a} ×ˢ T := by
  ext ⟨x, y⟩
  simp only [mem_fiber, Finset.mem_product, Finset.mem_singleton]
  aesop

theorem energyNorm_first_product_fiber (S : Finset G) (T : Finset H)
    (y : (S ×ˢ T).image Prod.fst) :
    energyNorm (fiber (S ×ˢ T) Prod.fst y.val) = energyNorm T := by
  have hy : y.val ∈ S := Finset.subset_product_image_fst y.property
  rw [first_product_fiber T hy, energyNorm_product, energyNorm_singleton, one_mul]

theorem mean_log_norm_first_product_fibers (S : Finset G) (T : Finset H)
    (ν : (S ×ˢ T) → ℝ) (hs : ∑ x, ν x = 1) :
    (∑ y, finitePush ν (imageEndpoint (S ×ˢ T) Prod.fst) y *
      Real.log (energyNorm (fiber (S ×ˢ T) Prod.fst y.val))) = Real.log (energyNorm T) := by
  simp only [energyNorm_first_product_fiber, ← Finset.sum_mul, finitePush_sum, hs, one_mul]

omit [AddCommGroup G] [AddCommGroup H] [DecidableEq H] in
/-- The actual first-coordinate marginal of uniform measure on a product
is uniform on the actual image support. -/
theorem uniform_product_first_marginal {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    finitePush (uniformReference (S ×ˢ T)) (imageEndpoint (S ×ˢ T) Prod.fst) =
      uniformReference ((S ×ˢ T).image Prod.fst) := by
  funext y
  have hy : y.val ∈ S := Finset.subset_product_image_fst y.property
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  rw [finitePush_imageEndpoint_eq_fiber]
  simp only [uniformReference, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, first_product_fiber T hy, Finset.card_product, Finset.card_singleton,
    Nat.one_mul, Nat.cast_mul, Finset.product_image_fst hT]
  field_simp

omit [AddCommGroup G] [AddCommGroup H] [DecidableEq H] in
theorem uniform_product_fiber_reference {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) (y : (S ×ˢ T).image Prod.fst) :
    imageFiberReference (S ×ˢ T) Prod.fst (uniformReference (S ×ˢ T)) y =
      uniformReference (fiber (S ×ˢ T) Prod.fst y.val) := by
  funext x
  have hy : y.val ∈ S := Finset.subset_product_image_fst y.property
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  simp only [imageFiberReference, uniform_product_first_marginal hS hT, uniformReference,
    first_product_fiber T hy, Finset.product_image_fst hT,
    Finset.card_product, Finset.card_singleton, Nat.one_mul, Nat.cast_mul]
  field_simp

theorem uniformEnergyWeight_product_energy (S : Finset G) (T : Finset H) :
    weightedEnergy (S ×ˢ T) (extendWeight (S ×ˢ T) (uniformEnergyWeight (S ×ˢ T))) =
      weightedEnergy S (extendWeight S (uniformEnergyWeight S)) *
        weightedEnergy T (extendWeight T (uniformEnergyWeight T)) := by
  simp only [uniformEnergyWeight_energy, countingEnergy_product, Finset.card_product,
    Nat.cast_mul, mul_pow, mul_div_mul_comm]

theorem uniformEnergyWeight_product_maximizes {S : Finset G} {T : Finset H}
    (hS : weightedEnergy S (extendWeight S (uniformEnergyWeight S)) = energyNorm S)
    (hT : weightedEnergy T (extendWeight T (uniformEnergyWeight T)) = energyNorm T) :
    weightedEnergy (S ×ˢ T) (extendWeight (S ×ˢ T) (uniformEnergyWeight (S ×ˢ T))) = energyNorm (S ×ˢ T) := by
  rw [uniformEnergyWeight_product_energy, hS, hT, energyNorm_product]

end
end Erdos539Geometry
