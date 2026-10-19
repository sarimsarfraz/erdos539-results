/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductSupportLaws
import Erdos539.StationaryEntropyMaximum

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

namespace StationaryAdditiveLaw
variable {S : Finset G} {T : Finset H} {ν : S → ℝ} {η : T → ℝ}

def productWeights (Q : StationaryAdditiveLaw S ν) (P : StationaryAdditiveLaw T η) :
    ((S ×ˢ T) × (S ×ˢ T)) × ((S ×ˢ T) × (S ×ˢ T)) → ℝ :=
  finitePush (finiteProductWeight Q.flat P.flat) (productQuadrupleEquiv S T)

theorem productWeights_mem (Q : StationaryAdditiveLaw S ν) (P : StationaryAdditiveLaw T η) :
    Q.productWeights P ∈ stationaryAdditiveWeights (S ×ˢ T) (productSupportLaw S T ν η) := by
  refine ⟨finitePush_nonneg _ _ (finiteProductWeight_nonneg Q.flat P.flat
    (fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2) (fun z ↦ P.nonneg z.1.1 z.1.2 z.2.1 z.2.2)), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply finitePush_eq_zero_of_fiber_zero
    intro w hw
    by_cases hQ : w.1.1.1.val + w.1.1.2.val = w.1.2.1.val + w.1.2.2.val
    · by_cases hP : w.2.1.1.val + w.2.1.2.val = w.2.2.1.val + w.2.2.2.val
      · rw [← hw] at hz
        exact (hz (Prod.ext hQ hP)).elim
      · change Q.flat w.1 * P.mass w.2.1.1 w.2.1.2 w.2.2.1 w.2.2.2 = 0
        rw [P.supported _ _ _ _ hP, mul_zero]
    · change Q.mass w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2 * P.flat w.2 = 0
      rw [Q.supported _ _ _ _ hQ, zero_mul]
  · rw [productWeights, finitePush_comp]
    change finitePush (finiteProductWeight Q.flat P.flat)
      ((productSupportEquiv S T) ∘ Prod.map (fun z ↦ z.1.1) (fun z ↦ z.1.1)) = _
    rw [← finitePush_comp, finitePush_productMap, Q.flat_first, P.flat_first, finitePush_productSupportEquiv]
  · rw [productWeights, finitePush_comp]
    change finitePush (finiteProductWeight Q.flat P.flat)
      ((productSupportEquiv S T) ∘ Prod.map (fun z ↦ z.1.2) (fun z ↦ z.1.2)) = _
    rw [← finitePush_comp, finitePush_productMap, Q.flat_second, P.flat_second, finitePush_productSupportEquiv]
  · rw [productWeights, finitePush_comp]
    change finitePush (finiteProductWeight Q.flat P.flat)
      ((productSupportEquiv S T) ∘ Prod.map (fun z ↦ z.2.1) (fun z ↦ z.2.1)) = _
    rw [← finitePush_comp, finitePush_productMap, Q.flat_third, P.flat_third, finitePush_productSupportEquiv]
  · rw [productWeights, finitePush_comp]
    change finitePush (finiteProductWeight Q.flat P.flat)
      ((productSupportEquiv S T) ∘ Prod.map (fun z ↦ z.2.2) (fun z ↦ z.2.2)) = _
    rw [← finitePush_comp, finitePush_productMap, Q.flat_fourth, P.flat_fourth, finitePush_productSupportEquiv]

/-- Independent actual stationary quadruples form an actual stationary
quadruple on the Cartesian product support. -/
def product (Q : StationaryAdditiveLaw S ν) (P : StationaryAdditiveLaw T η) :
    StationaryAdditiveLaw (S ×ˢ T) (productSupportLaw S T ν η) := ofFlat (Q.productWeights_mem P)

theorem product_entropy (Q : StationaryAdditiveLaw S ν) (P : StationaryAdditiveLaw T η)
    (hνs : ∑ x, ν x = 1) (hηs : ∑ y, η y = 1) : (Q.product P).entropy = Q.entropy + P.entropy := by
  have hQ : ∑ z, Q.flat z = 1 := by
    simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hνs
  have hP : ∑ z, P.flat z = 1 := by
    simpa only [flat, Fintype.sum_prod_type] using P.total_mass hηs
  rw [product, ofFlat_entropy, productWeights,
    finiteEntropy_push_eq_of_support_injective _ (productQuadrupleEquiv S T)
      (fun a b _ _ he ↦ (productQuadrupleEquiv S T).injective he),
    finiteProductWeight_entropy Q.flat P.flat hQ hP]
  simp only [finiteEntropy, entropy, flat, Fintype.sum_prod_type]

end StationaryAdditiveLaw
end
end Erdos539Geometry
