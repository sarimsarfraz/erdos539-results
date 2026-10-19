/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryProductLaw
import Erdos539.StationaryOptimizedProfile
import Erdos539.FiniteEntropySubadditive

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

namespace StationaryAdditiveLaw
variable {S : Finset G} {T : Finset H} {ρ : (S ×ˢ T) → ℝ}

def productFirst (Q : StationaryAdditiveLaw (S ×ˢ T) ρ) :
    StationaryAdditiveLaw S (finitePush ρ (productSupportFirst S T)) :=
  Q.map (productSupportFirst S T) (fun _ _ _ _ h ↦ congrArg Prod.fst h)

def productSecond (Q : StationaryAdditiveLaw (S ×ˢ T) ρ) :
    StationaryAdditiveLaw T (finitePush ρ (productSupportSecond S T)) :=
  Q.map (productSupportSecond S T) (fun _ _ _ _ h ↦ congrArg Prod.snd h)

/-- Any actual stationary quadruple on a product has entropy at most
the sum of its two actual coordinate-quadruple entropies. -/
theorem entropy_le_product_projections (Q : StationaryAdditiveLaw (S ×ˢ T) ρ)
    (hs : ∑ z, ρ z = 1) : Q.entropy ≤ Q.productFirst.entropy + Q.productSecond.entropy := by
  let R := finitePush Q.flat (productQuadrupleEquiv S T).symm
  have hR : ∀ z, 0 ≤ R z := finitePush_nonneg _ _ (fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2)
  have hRs : ∑ z, R z = 1 := by
    rw [finitePush_sum]
    simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hs
  have he : finiteEntropy R = Q.entropy := by
    rw [finiteEntropy_push_eq_of_support_injective Q.flat (productQuadrupleEquiv S T).symm
      (fun a b _ _ h ↦ (productQuadrupleEquiv S T).symm.injective h)]
    simp only [finiteEntropy, entropy, flat, Fintype.sum_prod_type]
  have hfirst : finitePush R Prod.fst = Q.productFirst.flat := by
    rw [finitePush_comp]
    rfl
  have hsecond : finitePush R Prod.snd = Q.productSecond.flat := by
    rw [finitePush_comp]
    rfl
  have h := finiteEntropy_subadditive R hR hRs
  rw [he, hfirst, hsecond] at h
  simpa only [finiteEntropy, entropy, flat, Fintype.sum_prod_type] using h

end StationaryAdditiveLaw

/-- Exact product additivity of the optimized stationary additive entropy,
with the actual independent law on the Cartesian product support. -/
theorem stationaryAdditiveEntropy_product (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hη : ∀ y, 0 ≤ η y) (hνs : ∑ x, ν x = 1) (hηs : ∑ y, η y = 1) :
    stationaryAdditiveEntropy (S ×ˢ T) (productSupportLaw S T ν η) =
      stationaryAdditiveEntropy S ν + stationaryAdditiveEntropy T η := by
  have hρ := productSupportLaw_nonneg S T ν η hν hη
  have hρs := productSupportLaw_sum S T ν η hνs hηs
  apply le_antisymm
  · obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained (S ×ˢ T) (productSupportLaw S T ν η) hρ hρs
    have h := Q.entropy_le_product_projections hρs
    have hfirst := Q.productFirst.entropy_le_stationaryAdditiveEntropy
      (finitePush_nonneg _ _ hρ) (by rw [finitePush_sum, hρs])
    have hsecond := Q.productSecond.entropy_le_stationaryAdditiveEntropy
      (finitePush_nonneg _ _ hρ) (by rw [finitePush_sum, hρs])
    conv at hfirst => rhs; rw [productSupportLaw_first S T ν η hηs]
    conv at hsecond => rhs; rw [productSupportLaw_second S T ν η hνs]
    rw [hQ] at h
    linarith
  · obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hνs
    obtain ⟨P, hP⟩ := stationaryAdditiveEntropy_attained T η hη hηs
    have h := (Q.product P).entropy_le_stationaryAdditiveEntropy hρ hρs
    rw [Q.product_entropy P hνs hηs, hQ, hP] at h
    exact h

theorem stationaryEntropyDefect_product (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hη : ∀ y, 0 ≤ η y) (hνs : ∑ x, ν x = 1) (hηs : ∑ y, η y = 1) :
    stationaryEntropyDefect (S ×ˢ T) (productSupportLaw S T ν η) =
      stationaryEntropyDefect S ν + stationaryEntropyDefect T η := by
  simp only [stationaryEntropyDefect, stationaryAdditiveEntropy_product S T ν η hν hη hνs hηs,
    productSupportLaw_entropy S T ν η hνs hηs]
  ring

theorem stationaryEnergyProfile_product (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hη : ∀ y, 0 ≤ η y) (hνs : ∑ x, ν x = 1) (hηs : ∑ y, η y = 1) :
    stationaryEnergyProfile (S ×ˢ T) (productSupportLaw S T ν η) =
      stationaryEnergyProfile S ν + stationaryEnergyProfile T η := by
  simp only [stationaryEnergyProfile, stationaryAdditiveEntropy_product S T ν η hν hη hνs hηs,
    productSupportLaw_entropy S T ν η hνs hηs]
  ring

end
end Erdos539Geometry
