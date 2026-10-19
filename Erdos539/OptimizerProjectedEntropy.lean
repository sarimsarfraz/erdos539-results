/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GeometricMeanFiberEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance optimizerEntropyImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

omit [AddCommGroup G] [DecidableEq G] in
theorem imageRestrictedWeight_squareSum (S : Finset G) (φ : G → H) (f : S → ℝ) (y : S.image φ) :
    (∑ x, imageRestrictedWeight S φ f y x ^ 2) = finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) y := by
  unfold imageRestrictedWeight finitePush
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : φ x.val = y.val <;> simp [imageEndpoint, Subtype.ext_iff, hx]

/-- Every projected atom of an exact parent's canonical quadruple is
bounded by the product of the four square-root endpoint masses. -/
theorem optimizer_imageFlat_le_sqrt_product {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (φ : G → H) (i j k l : S.image φ) :
    (optimizerStationaryAdditiveLaw hS hf hE).imageFlat φ ((i, j), (k, l)) ≤
      Real.sqrt (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) i) *
      Real.sqrt (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) j) *
      Real.sqrt (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) k) *
      Real.sqrt (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ) l) := by
  let m := finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ)
  have hm : ∀ y, 0 ≤ m y := finitePush_nonneg _ _ (fun x ↦ sq_nonneg (f x))
  have hrow (y : S.image φ) : weightedEnergy S (extendWeight S (imageRestrictedWeight S φ f y)) ≤
      energyNorm S * (Real.sqrt (m y)) ^ 4 := by
    have h := energyNorm_bound S (imageRestrictedWeight S φ f y)
    rw [imageRestrictedWeight_squareSum] at h
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (hm y)]
    exact h
  have h := mixedWeightedEnergy_le_common_bound S
    (extendWeight S (imageRestrictedWeight S φ f i)) (extendWeight S (imageRestrictedWeight S φ f j))
    (extendWeight S (imageRestrictedWeight S φ f k)) (extendWeight S (imageRestrictedWeight S φ f l))
    (energyNorm_pos hS).le (Real.sqrt_nonneg (m i)) (Real.sqrt_nonneg (m j))
    (Real.sqrt_nonneg (m k)) (Real.sqrt_nonneg (m l)) (hrow i) (hrow j) (hrow k) (hrow l)
  change finitePush (fun z : (S × S) × (S × S) ↦
    additiveQuadrupleWeight S f z.1.1 z.1.2 z.2.1 z.2.2 / energyNorm S)
    (StationaryAdditiveLaw.mapFour (imageEndpoint S φ)) ((i, j), (k, l)) ≤ _
  rw [finitePush_div, additiveWeight_image_push]
  apply (div_le_iff₀ (energyNorm_pos hS)).mpr
  convert h using 1
  dsimp only [m]
  ring

variable [AddCommGroup H]

/-- An exact optimizing parent has nonnegative same-law projected energy
profile, even though its projection need not optimize the image support. -/
theorem optimizer_imageFlat_entropy_ge_two {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (φ : G →+ H) :
    2 * finiteEntropy (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ)) ≤
      finiteEntropy ((optimizerStationaryAdditiveLaw hS hf hE).imageFlat φ) := by
  let Q := optimizerStationaryAdditiveLaw hS hf hE
  let P := Q.map (imageEndpoint S φ) (imageEndpoint_preserves_additive S φ)
  let m := finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ)
  have hpoint (z : ((S.image φ) × (S.image φ)) × ((S.image φ) × (S.image φ))) :
      Q.imageFlat φ z * Real.log (Q.imageFlat φ z) ≤ Q.imageFlat φ z * ((1 / 2 : ℝ) *
        (Real.log (m z.1.1) + Real.log (m z.1.2) + Real.log (m z.2.1) + Real.log (m z.2.2))) := by
    by_cases hz : Q.imageFlat φ z = 0
    · simp only [hz, zero_mul, le_refl]
    have hzP : P.mass z.1.1 z.1.2 z.2.1 z.2.2 ≠ 0 := hz
    obtain ⟨hi, hj, hk, hl⟩ := P.positive_endpoints hzP
    change 0 < m z.1.1 at hi
    change 0 < m z.1.2 at hj
    change 0 < m z.2.1 at hk
    change 0 < m z.2.2 at hl
    have h := Real.log_le_log (lt_of_le_of_ne (Q.imageFlat_nonneg φ z) (Ne.symm hz))
      (optimizer_imageFlat_le_sqrt_product hS hf hE φ z.1.1 z.1.2 z.2.1 z.2.2)
    have he : Real.log (Real.sqrt (m z.1.1) * Real.sqrt (m z.1.2) * Real.sqrt (m z.2.1) * Real.sqrt (m z.2.2)) =
        (1 / 2 : ℝ) * (Real.log (m z.1.1) + Real.log (m z.1.2) + Real.log (m z.2.1) + Real.log (m z.2.2)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_sqrt hi.le, Real.log_sqrt hj.le,
        Real.log_sqrt hk.le, Real.log_sqrt hl.le]
      ring
    change Real.log (Q.imageFlat φ z) ≤ _ at h
    change Real.log (Q.imageFlat φ z) ≤ Real.log (Real.sqrt (m z.1.1) * Real.sqrt (m z.1.2) *
      Real.sqrt (m z.2.1) * Real.sqrt (m z.2.2)) at h
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h (Q.imageFlat_nonneg φ z)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun z _ ↦ hpoint z)
  rw [Q.imageFlat_endpoint_expectation_factor φ (1 / 2 : ℝ) (fun y ↦ Real.log (m y))] at hsum
  have hentropyQ : (∑ z, Q.imageFlat φ z * Real.log (Q.imageFlat φ z)) = -finiteEntropy (Q.imageFlat φ) := by
    simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [hentropyQ] at hsum
  change -finiteEntropy (Q.imageFlat φ) ≤ (4 * (1 / 2 : ℝ)) * ∑ y, m y * Real.log (m y) at hsum
  have hentropym : (∑ y, m y * Real.log (m y)) = -finiteEntropy m := by
    simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [hentropym] at hsum
  change 2 * finiteEntropy m ≤ finiteEntropy (Q.imageFlat φ)
  linarith

theorem optimizer_image_energyProfile_bounds {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (φ : G →+ H) :
    0 ≤ finiteEntropy ((optimizerStationaryAdditiveLaw hS hf hE).imageFlat φ) -
      2 * finiteEntropy (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ)) ∧
    finiteEntropy ((optimizerStationaryAdditiveLaw hS hf hE).imageFlat φ) -
      2 * finiteEntropy (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ)) ≤
      stationaryEnergyProfile (S.image φ) (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S φ)) := by
  refine ⟨sub_nonneg.mpr (optimizer_imageFlat_entropy_ge_two hS hf hE φ), ?_⟩
  let Q := (optimizerStationaryAdditiveLaw hS hf hE).map (imageEndpoint S φ) (imageEndpoint_preserves_additive S φ)
  have h := Q.energyProfile_le_optimized (finitePush_nonneg _ _ (fun x ↦ sq_nonneg (f x)))
    (by rw [finitePush_sum, hf.2])
  simpa only [Q, StationaryAdditiveLaw.energyProfile, StationaryAdditiveLaw.entropy,
    StationaryAdditiveLaw.imageFlat, StationaryAdditiveLaw.map, finiteEntropy, Fintype.sum_prod_type] using h

end
end Erdos539Geometry
