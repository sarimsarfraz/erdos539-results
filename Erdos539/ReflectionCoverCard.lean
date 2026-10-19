/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionRatioTransport

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]

theorem reflected_cover_ratio {P A E : Finset G} (hP : P.Nonempty)
    {m : ℝ} (hm : 0 < m)
    (hR : ∀ z, energyNorm (reflectedSupport P z) ≤ energyNorm P * (24 / m ^ 2))
    (hAP : A ⊆ P) (w : ι → G)
    (hcover : ∀ x ∈ E, ∃ i, x ∈ reflectedSupport A (w i)) :
    energyNorm E / energyNorm P ≤ 24 * (Fintype.card ι : ℝ) ^ 2 / m ^ 2 := by
  have h := reflected_cover_norm_bound hAP w hcover (by positivity : (0 : ℝ) ≤ 24 / m ^ 2) hR
  apply (div_le_iff₀ (energyNorm_pos hP)).mpr
  convert h using 1
  ring

/-- Retaining a fraction theta of the norm requires at least
m sqrt(theta/24) reflected cores, even after arbitrary preliminary deletion. -/
theorem reflected_cover_card_lower {P A E : Finset G} (hP : P.Nonempty)
    {m : ℝ} (hm : 0 < m)
    (hR : ∀ z, energyNorm (reflectedSupport P z) ≤ energyNorm P * (24 / m ^ 2))
    (hAP : A ⊆ P) (w : ι → G)
    (hcover : ∀ x ∈ E, ∃ i, x ∈ reflectedSupport A (w i))
    {θ : ℝ} (hθ : 0 ≤ θ) (hretain : θ ≤ energyNorm E / energyNorm P) :
    m * Real.sqrt (θ / 24) ≤ (Fintype.card ι : ℝ) := by
  have hb := hretain.trans (reflected_cover_ratio hP hm hR hAP w hcover)
  have hb' := (le_div_iff₀ (pow_pos hm 2)).mp hb
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ θ / 24)
  have hn := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
  have hp := mul_nonneg hm.le (Real.sqrt_nonneg (θ / 24))
  nlinarith [sq_nonneg (m * Real.sqrt (θ / 24) - (Fintype.card ι : ℝ))]

end
end Erdos539Geometry
