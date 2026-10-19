/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MarginalEndpoints
import Erdos539.SharpExponentBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
local instance weightedCutHypothesisDecidableEq (ι : Type) : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The unproved weighted projection-balance conjecture, stated for arbitrary
finite coordinate labels. One exact optimizer supplies both marginal energies,
and the complementary cut is allowed to have an empty block. -/
def WeightedProjectionBalanceHypothesis (B : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ S : Finset (ι → ℝ), S.Nonempty →
    ∃ f : S → ℝ, f ∈ admissibleWeights S ∧
      weightedEnergy S (extendWeight S f) = energyNorm S ∧
      ∃ I J : Finset ι, Disjoint I J ∧ I ∪ J = Finset.univ ∧
        actualMarginalEnergy S (extendWeight S f) I ≤ Real.exp (B * Fintype.card ι) * maxFan S ∧
        actualMarginalEnergy S (extendWeight S f) J ≤ Real.exp (B * Fintype.card ι) * maxFan S

end
end Erdos539Geometry
