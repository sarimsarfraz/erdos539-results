/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.UniformProductFibers
import Erdos539.GeometricMeanFiberEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem sqrt_uniformReference (S : Finset G) :
    (fun x ↦ Real.sqrt (uniformReference S x)) = uniformEnergyWeight S := by
  funext x
  simp only [uniformReference, uniformEnergyWeight, one_div, Real.sqrt_inv]

omit [AddCommGroup H] [DecidableEq H] in
theorem countingEnergy_singleton (a : G) : countingEnergy {a} = 1 := by
  have hs : HasSidonSums ({a} : Finset G) := by
    intro b hb c hc d hd e he _
    simp only [Finset.mem_singleton] at hb hc hd he
    subst b; subst c; subst d; subst e
    exact Or.inl ⟨rfl, rfl⟩
  norm_num [countingEnergy_sidon hs]

theorem uniform_product_imageConditionalEnergy {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) (y : (S ×ˢ T).image Prod.fst) :
    imageConditionalEnergy (S ×ˢ T) Prod.fst (uniformReference (S ×ˢ T)) y =
      weightedEnergy T (extendWeight T (uniformEnergyWeight T)) := by
  have hy : y.val ∈ S := Finset.subset_product_image_fst y.property
  rw [imageConditionalEnergy, uniform_product_fiber_reference hS hT,
    sqrt_uniformReference, uniformEnergyWeight_energy, first_product_fiber T hy,
    countingEnergy_product, countingEnergy_singleton, Finset.card_product,
    Finset.card_singleton, Nat.one_mul, one_mul, uniformEnergyWeight_energy]

/-- Literal conditional energies of the uniform product are constant;
no replacement by fiber maximizing laws is made. -/
theorem uniform_product_mean_log_conditional_energy {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (∑ y, finitePush (uniformReference (S ×ˢ T)) (imageEndpoint (S ×ˢ T) Prod.fst) y *
      Real.log (imageConditionalEnergy (S ×ˢ T) Prod.fst (uniformReference (S ×ˢ T)) y)) =
      Real.log (weightedEnergy T (extendWeight T (uniformEnergyWeight T))) := by
  simp only [uniform_product_imageConditionalEnergy hS hT, ← Finset.sum_mul,
    finitePush_sum, uniformReference_sum (hS.product hT), one_mul]

omit [AddCommGroup G] [AddCommGroup H] [DecidableEq H] in
theorem uniform_product_first_entropy {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    finiteEntropy (finitePush (uniformReference (S ×ˢ T)) (imageEndpoint (S ×ˢ T) Prod.fst)) =
      Real.log (S.card : ℝ) := by
  rw [uniform_product_first_marginal hS hT, uniformReference_entropy ((hS.product hT).image _),
    Finset.product_image_fst hT]

end
end Erdos539Geometry
