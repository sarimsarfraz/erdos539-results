/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanEntropyDefect
import Erdos539.FourBlockInformation

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*}
local instance fanFourInformationDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

local instance fanObservationLabelDecidableEq : DecidableEq (Fin 4) := Classical.decEq _

namespace StationaryAdditiveLaw
variable {S : Finset (ι → ℝ)} {ν : S → ℝ}

/-- The four literal observations C,Z,D,W, in a common finite alphabet. -/
def fanObservation (S : Finset (ι → ℝ)) : Fin 4 → ((S × S) × (S × S)) → S ⊕ posDiff S :=
  ![fun t ↦ Sum.inl t.2.1,
    fun t ↦ Sum.inr (positiveDifferenceChannel S t.2.1 t.1.1),
    fun t ↦ Sum.inl t.2.2,
    fun t ↦ Sum.inr (positiveDifferenceChannel S t.2.2 t.1.2)]

def fanObservationEntropy (Q : StationaryAdditiveLaw S ν) : Finset (Fin 4) → ℝ :=
  observationEntropy Q.flat (fanObservation S)

theorem fanObservationEntropy_left (Q : StationaryAdditiveLaw S ν) :
    Q.fanObservationEntropy ({0} ∪ {1}) = finiteEntropy Q.leftFanJoint := by
  apply finiteEntropy_push_eq_of_fibers Q.flat (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
  intro t u
  rw [maskObservation_eq_iff]
  simp [fanObservation, quadrupleFanEncoding, Prod.ext_iff]

theorem fanObservationEntropy_right (Q : StationaryAdditiveLaw S ν) :
    Q.fanObservationEntropy ({2} ∪ {3}) = finiteEntropy Q.rightFanJoint := by
  apply finiteEntropy_push_eq_of_fibers Q.flat (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
  intro t u
  rw [maskObservation_eq_iff]
  simp [fanObservation, quadrupleFanEncoding, Prod.ext_iff]

theorem fanObservationEntropy_all (Q : StationaryAdditiveLaw S ν) :
    Q.fanObservationEntropy (({0} ∪ {1}) ∪ ({2} ∪ {3})) =
      finiteEntropy (finitePush Q.flat (quadrupleFanEncoding S)) := by
  apply finiteEntropy_push_eq_of_fibers Q.flat (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
  intro t u
  rw [maskObservation_eq_iff]
  simp [fanObservation, quadrupleFanEncoding, Prod.ext_iff, and_assoc, and_left_comm]

theorem fanObservationEntropy_empty (Q : StationaryAdditiveLaw S ν) (hs : ∑ x, ν x = 1) :
    Q.fanObservationEntropy ∅ = 0 := by
  apply observationEntropy_empty Q.flat (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
  simp only [flat, Fintype.sum_prod_type]
  exact Q.total_mass hs

theorem fanPairInformation_eq_maskCMI (Q : StationaryAdditiveLaw S ν) (hs : ∑ x, ν x = 1) :
    Q.fanPairInformation = maskCMI Q.fanObservationEntropy ({0} ∪ {1}) ({2} ∪ {3}) ∅ := by
  simp only [maskCMI, Finset.union_empty, Q.fanObservationEntropy_left,
    Q.fanObservationEntropy_right, Q.fanObservationEntropy_empty hs,
    Q.fanObservationEntropy_all, sub_zero, fanPairInformation]

/-- I((C,Z);(D,W)) = I(C;D)+I(Z;D|C)+I(W;C|D)+I(Z;W|C,D). -/
theorem fanPairInformation_four_terms (Q : StationaryAdditiveLaw S ν) (hs : ∑ x, ν x = 1) :
    Q.fanPairInformation =
      maskCMI Q.fanObservationEntropy {0} {2} ∅ +
      maskCMI Q.fanObservationEntropy {1} {2} {0} +
      maskCMI Q.fanObservationEntropy {3} {0} {2} +
      maskCMI Q.fanObservationEntropy {1} {3} ({0} ∪ {2}) := by
  rw [Q.fanPairInformation_eq_maskCMI hs]
  exact four_block_information_identity _ (Q.fanObservationEntropy_empty hs) _ _ _ _

theorem fanPairInformation_four_terms_nonneg (Q : StationaryAdditiveLaw S ν) :
    0 ≤ maskCMI Q.fanObservationEntropy {0} {2} ∅ ∧
    0 ≤ maskCMI Q.fanObservationEntropy {1} {2} {0} ∧
    0 ≤ maskCMI Q.fanObservationEntropy {3} {0} {2} ∧
    0 ≤ maskCMI Q.fanObservationEntropy {1} {3} ({0} ∪ {2}) :=
  observation_four_information_terms Q.flat
    (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2) (fanObservation S) _ _ _ _

end StationaryAdditiveLaw

theorem exists_fanEntropyDefect_four_information_terms (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    ∃ Q : StationaryAdditiveLaw S ν, Q.entropy = stationaryAdditiveEntropy S ν ∧
      0 ≤ Q.leftFanSlack ∧
      fanEntropyDefect S ν = 2 * Q.leftFanSlack +
        (maskCMI Q.fanObservationEntropy {0} {2} ∅ +
         maskCMI Q.fanObservationEntropy {1} {2} {0} +
         maskCMI Q.fanObservationEntropy {3} {0} {2} +
         maskCMI Q.fanObservationEntropy {1} {3} ({0} ∪ {2})) := by
  obtain ⟨Q, hQ, hR, _hI, he⟩ := exists_fanEntropyDefect_decomposition S ν hν hs
  refine ⟨Q, hQ, hR, ?_⟩
  rw [he, Q.fanPairInformation_four_terms hs]

end
end Erdos539Geometry
