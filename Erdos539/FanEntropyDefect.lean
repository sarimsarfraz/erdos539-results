/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.QuadrupleFanEncoding
import Erdos539.StationaryPairSymmetry

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*}
local instance fanEntropyDefectDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The manuscript's D1: two stationary fan capacities minus endpoint
entropy, plus the stationary additive-entropy deficiency. -/
def fanEntropyDefect (S : Finset (ι → ℝ)) (ν : S → ℝ) : ℝ :=
  2 * stationaryFanCapacity S ν - finiteEntropy ν + stationaryEntropyDefect S ν

theorem fanEntropyDefect_nonneg (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : 0 ≤ fanEntropyDefect S ν := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have h := Q.entropy_le_two_fans hν hs
  unfold fanEntropyDefect stationaryEntropyDefect
  rw [← hQ]
  linarith

namespace StationaryAdditiveLaw
variable {S : Finset (ι → ℝ)} {ν : S → ℝ}

def leftFanJoint (Q : StationaryAdditiveLaw S ν) : S × posDiff S → ℝ :=
  finitePush Q.flat (fun t ↦ (quadrupleFanEncoding S t).1)

def rightFanJoint (Q : StationaryAdditiveLaw S ν) : S × posDiff S → ℝ :=
  finitePush Q.flat (fun t ↦ (quadrupleFanEncoding S t).2)

def leftFanSlack (Q : StationaryAdditiveLaw S ν) : ℝ :=
  stationaryFanCapacity S ν - (finiteEntropy Q.leftFanJoint - finiteEntropy ν)

def rightFanSlack (Q : StationaryAdditiveLaw S ν) : ℝ :=
  stationaryFanCapacity S ν - (finiteEntropy Q.rightFanJoint - finiteEntropy ν)

def fanPairInformation (Q : StationaryAdditiveLaw S ν) : ℝ :=
  finiteEntropy Q.leftFanJoint + finiteEntropy Q.rightFanJoint -
    finiteEntropy (finitePush Q.flat (quadrupleFanEncoding S))

theorem leftFanSlack_nonneg (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : 0 ≤ Q.leftFanSlack := by
  have h := Q.endpoint_fan_entropy_le hν hs (fun t ↦ t.2.1) (fun t ↦ t.1.1)
    Q.flat_third Q.flat_first
  change finiteEntropy Q.leftFanJoint ≤ finiteEntropy ν + stationaryFanCapacity S ν at h
  unfold leftFanSlack
  linarith

theorem rightFanSlack_nonneg (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : 0 ≤ Q.rightFanSlack := by
  have h := Q.endpoint_fan_entropy_le hν hs (fun t ↦ t.2.2) (fun t ↦ t.1.2)
    Q.flat_fourth Q.flat_second
  change finiteEntropy Q.rightFanJoint ≤ finiteEntropy ν + stationaryFanCapacity S ν at h
  unfold rightFanSlack
  linarith

theorem fanPairInformation_nonneg (Q : StationaryAdditiveLaw S ν)
    (hs : ∑ x, ν x = 1) : 0 ≤ Q.fanPairInformation := by
  have hp := finitePush_nonneg Q.flat (quadrupleFanEncoding S)
    (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
  have hmass : ∑ t, Q.flat t = 1 := by
    simp only [flat, Fintype.sum_prod_type]
    exact Q.total_mass hs
  have h := finiteEntropy_subadditive (finitePush Q.flat (quadrupleFanEncoding S)) hp
    (by rw [finitePush_sum, hmass])
  rw [finitePush_comp, finitePush_comp] at h
  change finiteEntropy (finitePush Q.flat (quadrupleFanEncoding S)) ≤
    finiteEntropy Q.leftFanJoint + finiteEntropy Q.rightFanJoint at h
  unfold fanPairInformation
  linarith

theorem fan_defect_decomposition (Q : StationaryAdditiveLaw S ν)
    (hQ : Q.entropy = stationaryAdditiveEntropy S ν) :
    fanEntropyDefect S ν = Q.leftFanSlack + Q.rightFanSlack + Q.fanPairInformation := by
  unfold fanEntropyDefect stationaryEntropyDefect leftFanSlack rightFanSlack fanPairInformation
  rw [Q.fan_encoding_entropy, hQ]
  ring

theorem fan_joints_eq_of_pair_symmetry (Q : StationaryAdditiveLaw S ν)
    (hQ : ∀ a b c d, Q.mass a b c d = Q.mass b a d c) :
    Q.leftFanJoint = Q.rightFanJoint := by
  funext z
  unfold leftFanJoint rightFanJoint finitePush
  apply Fintype.sum_equiv (Equiv.prodCongr (Equiv.prodComm S S) (Equiv.prodComm S S))
  intro t
  simp only [quadrupleFanEncoding, Equiv.prodCongr_apply, Prod.map, Equiv.prodComm_apply, Prod.swap, flat]
  rw [hQ t.1.1 t.1.2 t.2.1 t.2.2]

end StationaryAdditiveLaw

/-- The exact nonnegative D1=2R+I identity for an attained symmetric
maximizer, with both terms defined from its literal fan observations. -/
theorem exists_fanEntropyDefect_decomposition (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    ∃ Q : StationaryAdditiveLaw S ν, Q.entropy = stationaryAdditiveEntropy S ν ∧
      0 ≤ Q.leftFanSlack ∧ 0 ≤ Q.fanPairInformation ∧
      fanEntropyDefect S ν = 2 * Q.leftFanSlack + Q.fanPairInformation := by
  obtain ⟨Q, hQ, hsym⟩ := exists_pair_symmetric_stationary_maximum S ν hν hs
  refine ⟨Q, hQ, Q.leftFanSlack_nonneg hν hs, Q.fanPairInformation_nonneg hs, ?_⟩
  have he := Q.fan_joints_eq_of_pair_symmetry hsym
  have hslack : Q.rightFanSlack = Q.leftFanSlack := by
    unfold StationaryAdditiveLaw.rightFanSlack StationaryAdditiveLaw.leftFanSlack
    rw [he]
  rw [Q.fan_defect_decomposition hQ, hslack]
  ring

end
end Erdos539Geometry
