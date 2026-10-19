/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteConditionalEntropy
import Erdos539.Fans

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance stationaryFanCapacityDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

def positiveDifferenceChannel (S : Finset (ι → ℝ)) (a x : S) : posDiff S :=
  ⟨pdiff x.val a.val, mem_posDiff.mpr ⟨x.val, x.property, a.val, a.property, rfl⟩⟩

def fanOutputs (S : Finset (ι → ℝ)) (a : S) : Finset (posDiff S) :=
  Finset.univ.filter (fun z ↦ z.val ∈ fan S a.val)

theorem positiveDifferenceChannel_mem_fanOutputs (S : Finset (ι → ℝ)) (a x : S) :
    positiveDifferenceChannel S a x ∈ fanOutputs S a := by
  simp only [fanOutputs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_fan.mpr ⟨x.val, x.property, rfl⟩

theorem fanOutputs_nonempty (S : Finset (ι → ℝ)) (a : S) : (fanOutputs S a).Nonempty :=
  ⟨positiveDifferenceChannel S a a, positiveDifferenceChannel_mem_fanOutputs S a a⟩

theorem fanOutputs_card (S : Finset (ι → ℝ)) (a : S) : (fanOutputs S a).card = (fan S a.val).card := by
  apply Finset.card_bij (fun z _ ↦ z.val)
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro x _ y _ h
    exact Subtype.ext h
  · intro z hz
    refine ⟨⟨z, fan_subset_posDiff a.property hz⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩

/-- The manuscript's actual stationary fan capacity: maximize conditional
positive-difference entropy over all couplings with the given two marginals. -/
def stationaryFanCapacity (S : Finset (ι → ℝ)) (ν : S → ℝ) : ℝ :=
  stationaryCapacity ν (positiveDifferenceChannel S)

theorem stationaryFanCapacity_attained (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    ∃ p ∈ stationaryCouplings ν,
      couplingOutputEntropy ν (positiveDifferenceChannel S) p = stationaryFanCapacity S ν :=
  stationaryCapacity_attained ν hν hs (positiveDifferenceChannel S)

theorem stationaryFanCapacity_bounds (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    0 ≤ stationaryFanCapacity S ν ∧ stationaryFanCapacity S ν ≤ finiteEntropy ν :=
  stationaryCapacity_bounds ν hν hs (positiveDifferenceChannel S)

/-- The actual stationary fan value is bounded by the logarithm of the
actual maximum anchored fan, with zero atoms allowed. -/
theorem stationaryFanCapacity_le_log_maxFan (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    stationaryFanCapacity S ν ≤ Real.log (maxFan S) := by
  have h := stationaryCapacity_le_log_rows ν hν hs (positiveDifferenceChannel S)
    (fanOutputs S) (fanOutputs_nonempty S) (positiveDifferenceChannel_mem_fanOutputs S)
  apply h.trans
  calc
    _ ≤ ∑ a, ν a * Real.log (maxFan S) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hν a)
      have hp : (0 : ℝ) < (fanOutputs S a).card := by exact_mod_cast (fanOutputs_nonempty S a).card_pos
      apply Real.log_le_log hp
      rw [fanOutputs_card]
      exact_mod_cast card_fan_le_maxFan a.property
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

end
end Erdos539Geometry
