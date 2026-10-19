/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanNormCalibrations

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*}
local instance fanNormDefectDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The literal D1 formulation of the norm improvement, with no positivity
restriction on the endpoint law. This is an equivalence, not a proof that
any exponent larger than two works in arbitrary dimension. -/
theorem fanNormBound_iff_defect {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {p C : ℝ} (hp : 0 < p) (hC : 0 < C) :
    FanNormBound S (positiveDifferenceChannel S) p C ↔
      ∀ ν : S → ℝ, (∀ a, 0 ≤ ν a) → (∑ a, ν a = 1) →
        (2 - 4 / p) * finiteEntropy ν - Real.log C ≤ fanEntropyDefect S ν := by
  rw [fanNormBound_iff_entropy hS _ hp hC]
  unfold FanEntropyBound
  constructor
  · intro h ν hν hs
    have hh := h ν hν hs
    change stationaryAdditiveEntropy S ν ≤
      2 * stationaryFanCapacity S ν + (4 / p) * finiteEntropy ν + Real.log C at hh
    unfold fanEntropyDefect stationaryEntropyDefect
    nlinarith
  · intro h ν hν hs
    have hh := h ν hν hs
    unfold fanEntropyDefect stationaryEntropyDefect at hh
    change stationaryAdditiveEntropy S ν ≤
      2 * stationaryFanCapacity S ν + (4 / p) * finiteEntropy ν + Real.log C
    nlinarith

end
end Erdos539Geometry
