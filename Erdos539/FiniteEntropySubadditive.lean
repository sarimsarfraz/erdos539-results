/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteConditioning

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Subadditivity for a finite joint probability law, including zero
atoms and distinct endpoint alphabets. -/
theorem finiteEntropy_subadditive {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) (hs : ∑ z, p z = 1) :
    finiteEntropy p ≤ finiteEntropy (finitePush p Prod.fst) + finiteEntropy (finitePush p Prod.snd) := by
  have hsum : ∑ z, pairMarginalReference p z = 1 := by
    simp only [pairMarginalReference, Fintype.sum_prod_type, ← Finset.mul_sum,
      finitePush_sum, hs, mul_one]
  have hr := finiteRelEntropy_nonneg p (pairMarginalReference p) hp
    (pairMarginalReference_nonneg p hp) hs hsum (pairMarginalReference_pos p hp)
  rw [finiteRelEntropy_pairMarginalReference p hp] at hr
  linarith

end
end Erdos539Geometry
