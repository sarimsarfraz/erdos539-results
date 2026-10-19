/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionCoverCard
import Erdos539.SparseReflectionProductExistence

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
local instance reflectionCoverEntropyRealDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _

/-- A positive fraction of the norm requires exponentially many reflected
supports in the actual optimizer defect; the constant is explicit. -/
theorem reflection_cover_card_exponential {ι : Type*} [Fintype ι]
    {P A E : Finset (ReflectionProductCoordinates → ℝ)} (hP : P.Nonempty)
    {m : ℝ} (hm : 0 < m) (hN : (P.card : ℝ) ≤ 54 * m * energyNorm P)
    (hR : ∀ z, energyNorm (reflectedSupport P z) ≤ energyNorm P * (24 / m ^ 2))
    (hAP : A ⊆ P) (w : ι → (ReflectionProductCoordinates → ℝ))
    (hcover : ∀ x ∈ E, ∃ i, x ∈ reflectedSupport A (w i))
    {θ : ℝ} (hθ : 0 ≤ θ) (hretain : θ ≤ energyNorm E / energyNorm P)
    {f : P → ℝ} (hf : f ∈ admissibleWeights P)
    (hopt : weightedEnergy P (extendWeight P f) = energyNorm P) :
    Real.exp (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm P)) *
        Real.sqrt (θ / 24) / 54 ≤ (Fintype.card ι : ℝ) := by
  have hc := reflected_cover_card_lower hP hm hR hAP w hcover hθ hretain
  have he := (reflection_product_optimizer_bounds hP hm hN hR hf hopt).2.1
  have hexp := Real.exp_le_exp.mpr he
  rw [Real.exp_add, Real.exp_log hm, Real.exp_log (by norm_num : (0 : ℝ) < 54)] at hexp
  have hs := mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg (θ / 24))
  apply le_trans _ hc
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 54)).mpr
  nlinarith only [hs]

end
end Erdos539Geometry
