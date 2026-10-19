/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteIndependentPairs
import Erdos539.StationaryEntropyMaximum

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def independentSumLabel (S : Finset G) (z : S × S) : S + S :=
  ⟨z.1.val + z.2.val, Finset.mem_add.mpr ⟨z.1.val, z.1.property, z.2.val, z.2.property, rfl⟩⟩

def independentDifferenceLabel (S : Finset G) (z : S × S) : S - S :=
  ⟨z.1.val - z.2.val, Finset.mem_sub.mpr ⟨z.1.val, z.1.property, z.2.val, z.2.property, rfl⟩⟩

theorem sumCopy_mem_stationaryAdditiveWeights (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    sameFiberCoupling (independentPairWeight ν) (independentSumLabel S) ∈ stationaryAdditiveWeights S ν := by
  have hp : ∀ z, 0 ≤ independentPairWeight ν z := fun z ↦ mul_nonneg (hν z.1) (hν z.2)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := independentPairCoupling_marginals ν hs _
    (sameFiberCoupling_first _ hp (independentSumLabel S)) (sameFiberCoupling_second _ hp (independentSumLabel S))
  refine ⟨sameFiberCoupling_nonneg _ hp _, ?_, h₁, h₂, h₃, h₄⟩
  intro z hz
  have hn : independentSumLabel S z.1 ≠ independentSumLabel S z.2 := fun h ↦ hz (congrArg Subtype.val h)
  simp only [sameFiberCoupling, if_neg hn]

/-- The actual additive quadruple obtained by copying an independent pair
conditionally on its sum. -/
def sumStationaryWitness (S : Finset G) (ν : S → ℝ) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    StationaryAdditiveLaw S ν := StationaryAdditiveLaw.ofFlat (sumCopy_mem_stationaryAdditiveWeights S ν hν hs)

theorem sumStationaryWitness_entropy (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    (sumStationaryWitness S ν hν hs).entropy =
      4 * finiteEntropy ν - finiteEntropy (finitePush (independentPairWeight ν) (independentSumLabel S)) := by
  rw [sumStationaryWitness, StationaryAdditiveLaw.ofFlat_entropy,
    sameFiberCoupling_entropy (independentPairWeight ν) (fun z ↦ mul_nonneg (hν z.1) (hν z.2)) (independentSumLabel S),
    independentPairWeight_entropy ν hs]
  ring

omit [AddCommGroup G] [DecidableEq G] in
def exchangeSecondFourth (α : Type*) : ((α × α) × (α × α)) ≃ ((α × α) × (α × α)) where
  toFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  invFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def differenceCopyWeight (S : Finset G) (ν : S → ℝ) : (S × S) × (S × S) → ℝ :=
  finitePush (sameFiberCoupling (independentPairWeight ν) (independentDifferenceLabel S)) (exchangeSecondFourth S)

theorem differenceCopy_mem_stationaryAdditiveWeights (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : differenceCopyWeight S ν ∈ stationaryAdditiveWeights S ν := by
  let R := sameFiberCoupling (independentPairWeight ν) (independentDifferenceLabel S)
  have hp : ∀ z, 0 ≤ independentPairWeight ν z := fun z ↦ mul_nonneg (hν z.1) (hν z.2)
  have hR : ∀ z, 0 ≤ R z := sameFiberCoupling_nonneg _ hp _
  obtain ⟨h₁, h₂, h₃, h₄⟩ := independentPairCoupling_marginals ν hs R
    (sameFiberCoupling_first _ hp _) (sameFiberCoupling_second _ hp _)
  refine ⟨finitePush_nonneg R (exchangeSecondFourth S) hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply finitePush_eq_zero_of_fiber_zero
    intro w hw
    rw [← hw] at hz
    change w.1.1.val + w.2.2.val ≠ w.2.1.val + w.1.2.val at hz
    have hn : independentDifferenceLabel S w.1 ≠ independentDifferenceLabel S w.2 := by
      intro he
      have he' : w.1.1.val - w.1.2.val = w.2.1.val - w.2.2.val := congrArg Subtype.val he
      exact hz (sub_eq_sub_iff_add_eq_add.mp he')
    simp only [sameFiberCoupling, if_neg hn]
  · change finitePush (finitePush R (exchangeSecondFourth S)) (fun z ↦ z.1.1) = ν
    rw [finitePush_comp]
    exact h₁
  · change finitePush (finitePush R (exchangeSecondFourth S)) (fun z ↦ z.1.2) = ν
    rw [finitePush_comp]
    exact h₄
  · change finitePush (finitePush R (exchangeSecondFourth S)) (fun z ↦ z.2.1) = ν
    rw [finitePush_comp]
    exact h₃
  · change finitePush (finitePush R (exchangeSecondFourth S)) (fun z ↦ z.2.2) = ν
    rw [finitePush_comp]
    exact h₂

/-- The conditionally copied independent difference pair, with its
endpoints permuted into the additive-quadruple equation. -/
def differenceStationaryWitness (S : Finset G) (ν : S → ℝ) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    StationaryAdditiveLaw S ν := StationaryAdditiveLaw.ofFlat (differenceCopy_mem_stationaryAdditiveWeights S ν hν hs)

theorem differenceStationaryWitness_entropy (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    (differenceStationaryWitness S ν hν hs).entropy =
      4 * finiteEntropy ν - finiteEntropy (finitePush (independentPairWeight ν) (independentDifferenceLabel S)) := by
  rw [differenceStationaryWitness, StationaryAdditiveLaw.ofFlat_entropy, differenceCopyWeight,
    finiteEntropy_push_eq_of_support_injective _ (exchangeSecondFourth S)
      (fun a b _ _ he ↦ (exchangeSecondFourth S).injective he),
    sameFiberCoupling_entropy (independentPairWeight ν) (fun z ↦ mul_nonneg (hν z.1) (hν z.2)) (independentDifferenceLabel S),
    independentPairWeight_entropy ν hs]
  ring

theorem stationaryEntropyDefect_le_sum_growth (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    stationaryEntropyDefect S ν ≤ finiteEntropy (finitePush (independentPairWeight ν) (independentSumLabel S)) - finiteEntropy ν := by
  have h := (sumStationaryWitness S ν hν hs).entropy_le_stationaryAdditiveEntropy hν hs
  rw [sumStationaryWitness_entropy] at h
  unfold stationaryEntropyDefect
  linarith

theorem stationaryEntropyDefect_le_difference_growth (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    stationaryEntropyDefect S ν ≤ finiteEntropy (finitePush (independentPairWeight ν) (independentDifferenceLabel S)) - finiteEntropy ν := by
  have h := (differenceStationaryWitness S ν hν hs).entropy_le_stationaryAdditiveEntropy hν hs
  rw [differenceStationaryWitness_entropy] at h
  unfold stationaryEntropyDefect
  linarith

end
end Erdos539Geometry
