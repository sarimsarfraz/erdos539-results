/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyFibring
import Erdos539.StationaryProjectionProfile

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance optimizedProfileImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- The optimized stationary profile R(nu)=A(nu)-2H(nu). It is not
defined as a raw weighted energy. -/
def stationaryEnergyProfile (S : Finset G) (ν : S → ℝ) : ℝ :=
  stationaryAdditiveEntropy S ν - 2 * finiteEntropy ν

omit [DecidableEq G] [DecidableEq H] in
theorem stationaryEnergyProfile_eq_entropy_sub_defect (S : Finset G) (ν : S → ℝ) :
    stationaryEnergyProfile S ν = finiteEntropy ν - stationaryEntropyDefect S ν := by
  unfold stationaryEnergyProfile stationaryEntropyDefect
  ring

omit [DecidableEq G] [DecidableEq H] in
theorem stationaryEnergyProfile_bounds {S : Finset G} {ν : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    0 ≤ stationaryEnergyProfile S ν ∧ stationaryEnergyProfile S ν ≤ finiteEntropy ν := by
  obtain ⟨hl, hu⟩ := stationaryEntropyDefect_bounds S ν hν hs
  rw [stationaryEnergyProfile_eq_entropy_sub_defect]
  constructor <;> linarith

omit [DecidableEq H] in
theorem stationaryEnergyProfile_le_log_energy {S : Finset G} {ν : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    stationaryEnergyProfile S ν ≤ Real.log (weightedEnergy S (extendWeight S (fun x ↦ Real.sqrt (ν x)))) := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have h := Q.entropy_le_log_energy hν hs
  simpa only [hQ, stationaryEnergyProfile] using h

omit [DecidableEq H] in
theorem stationaryEnergyProfile_le_log_norm {S : Finset G} {ν : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    stationaryEnergyProfile S ν ≤ Real.log (energyNorm S) := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have h := Q.entropy_le_log_norm hν hs
  simpa only [hQ, stationaryEnergyProfile] using h

omit [DecidableEq G] [DecidableEq H] in
theorem StationaryAdditiveLaw.energyProfile_le_optimized {S : Finset G} {ν : S → ℝ}
    (Q : StationaryAdditiveLaw S ν) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    Q.energyProfile ≤ stationaryEnergyProfile S ν := by
  have h := Q.entropy_le_stationaryAdditiveEntropy hν hs
  unfold StationaryAdditiveLaw.energyProfile stationaryEnergyProfile
  linarith

omit [DecidableEq H] in
theorem stationaryEnergyProfile_optimizer {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    stationaryEnergyProfile S (fun x ↦ f x ^ 2) = Real.log (energyNorm S) := by
  have hl := (optimizerStationaryAdditiveLaw hS hf hE).energyProfile_le_optimized
    (fun x ↦ sq_nonneg (f x)) hf.2
  rw [optimizerStationaryAdditiveLaw_energyProfile hS hf hE] at hl
  exact le_antisymm (stationaryEnergyProfile_le_log_norm (fun x ↦ sq_nonneg (f x)) hf.2) hl

/-- The actual parent law controls the mean optimized profile of its
conditional endpoints through its literal projected quadruple entropy. -/
theorem StationaryAdditiveLaw.energyProfile_image_fibring {S : Finset G} {ν : S → ℝ}
    (Q : StationaryAdditiveLaw S ν) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (φ : G → H) :
    Q.energyProfile ≤ (finiteEntropy (Q.imageFlat φ) - 2 * finiteEntropy (finitePush ν (imageEndpoint S φ))) +
      ∑ y, finitePush ν (imageEndpoint S φ) y * stationaryEnergyProfile (fiber S φ y.val) (imageFiberReference S φ ν y) := by
  have h := Q.entropy_image_fibring hν hs φ
  have he := imageFiber_entropy_chain S φ ν hν
  unfold stationaryEnergyProfile StationaryAdditiveLaw.energyProfile
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hsum : (∑ y, finitePush ν (imageEndpoint S φ) y * (2 * finiteEntropy (imageFiberReference S φ ν y))) =
      2 * ∑ y, finitePush ν (imageEndpoint S φ) y * finiteEntropy (imageFiberReference S φ ν y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsum]
  linarith

variable [AddCommGroup H]

theorem stationaryEnergyProfile_subadditive {S : Finset G} {ν : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (φ : G →+ H) :
    stationaryEnergyProfile S ν ≤ stationaryEnergyProfile (S.image φ) (finitePush ν (imageEndpoint S φ)) +
      ∑ y, finitePush ν (imageEndpoint S φ) y * stationaryEnergyProfile (fiber S φ y.val) (imageFiberReference S φ ν y) := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have h := Q.energyProfile_image_fibring hν hs φ
  let P := Q.map (imageEndpoint S φ) (imageEndpoint_preserves_additive S φ)
  have hP := P.energyProfile_le_optimized (finitePush_nonneg ν (imageEndpoint S φ) hν)
    (by rw [finitePush_sum, hs])
  have he : finiteEntropy (Q.imageFlat φ) - 2 * finiteEntropy (finitePush ν (imageEndpoint S φ)) = P.energyProfile := by
    simp only [StationaryAdditiveLaw.imageFlat, StationaryAdditiveLaw.energyProfile,
      StationaryAdditiveLaw.entropy, P, StationaryAdditiveLaw.map, finiteEntropy, Fintype.sum_prod_type]
  have hroot : Q.energyProfile = stationaryEnergyProfile S ν := by
    simp only [StationaryAdditiveLaw.energyProfile, stationaryEnergyProfile, hQ]
  rw [he, hroot] at h
  linarith

end
end Erdos539Geometry
