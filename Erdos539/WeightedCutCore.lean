/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedCutInduction
import Erdos539.QuadraticCoreGrowth

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
local instance weightedCutCoreDecidableEq (D : ℕ) : DecidableEq (Fin D → ℝ) := Classical.decEq _

/-- The gap between the sharp fan exponent and the singleton criticality
bound absorbs the linear-in-dimension loss. -/
theorem weighted_cut_core_scalar {A D p u L Q : ℝ}
    (hA : 0 ≤ A) (hp : 0 < p) (hpD : p ≤ D) (hL : 0 ≤ L)
    (hu : 1 / 2 + 1 / (4 * p) ≤ u)
    (hfan : u * L - A * p ≤ Q)
    (hcrit : 2 * Q ≤ (1 + 1 / (4 * D)) * L) :
    L ≤ (8 * A) * D ^ 2 := by
  have hD : 0 < D := hp.trans_le hpD
  have hinv : 1 / (4 * D) ≤ 1 / (4 * p) := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hexp : 1 / 2 + 1 / (4 * D) ≤ u := by linarith
  have he := mul_le_mul_of_nonneg_right hexp hL
  have hgap : L / (4 * D) ≤ 2 * A * p := by
    linear_combination 2 * hfan + hcrit + 2 * he
  have hclear := (div_le_iff₀ (by positivity : 0 < 4 * D)).mp hgap
  have hsize := mul_le_mul_of_nonneg_left hpD (by positivity : 0 ≤ 8 * A * D)
  nlinarith

/-- The sufficient weighted-cut hypothesis implies the quadratic bound
for the literal cores selected from a positive-dimensional parent. -/
theorem WeightedProjectionBalanceHypothesis.quadratic_core {B : ℝ}
    (hcut : WeightedProjectionBalanceHypothesis B) (hB : 0 ≤ B) :
    QuadraticCoreHypothesis (8 * (B + Real.log 16)) := by
  intro D hD S hS I T h
  have hz : ∀ x ∈ T, ∀ i ∉ I, x i = 0 :=
    fun _ hx _ hi ↦ maskedProjection_zero_outside ((mem_projectionCandidates.mp h.1).2 hx) hi
  have hA : 0 ≤ B + Real.log 16 := add_nonneg hB (Real.log_nonneg (by norm_num))
  by_cases hp0 : I.card = 0
  · have hI : I = ∅ := Finset.card_eq_zero.mp hp0
    have he : T = {0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      obtain ⟨x, hx⟩ := h.nonempty
      have hzero : ∀ y ∈ T, y = 0 := by
        intro y hy
        ext i
        exact hz y hy i (by simp [hI])
      exact ⟨hzero x hx ▸ hx, hzero⟩
    rw [he, energyNorm_singleton, Real.log_one]
    positivity
  have hp : 0 < I.card := Nat.pos_of_ne_zero hp0
  have hproj : (projection T I).Nonempty := by
    simpa only [projection, Finset.image_nonempty] using h.nonempty
  have hnorm := energyNorm_projection_eq_of_zero_outside hz
  have hfan := hcut.log_fan_bound hB I.card hp I (by simp) (projection T I) hproj
  simp only [energyNorm_eq_classical] at hnorm hfan
  rw [hnorm] at hfan
  have hmax : maxFan (projection T I) ≤ (posDiff T).card := by
    have hm := maxFan_projection_slice_le T ∅ I 0
    simp only [slice_empty, maxRestrictedFan_empty] at hm
    exact hm.trans (maxFan_le_card_posDiff T)
  have hmpos : (0 : ℝ) < maxFan (projection T I) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hproj))
  have hlog := Real.log_le_log hmpos (show (maxFan (projection T I) : ℝ) ≤ (posDiff T).card by exact_mod_cast hmax)
  have hcrit := h.singleton_log_bound hS (by positivity : 0 < 4 * (D : ℝ))
  apply weighted_cut_core_scalar hA (by exact_mod_cast hp)
    (show (I.card : ℝ) ≤ D by exact_mod_cast (I.card_le_univ.trans_eq (Fintype.card_fin D)))
    (Real.log_nonneg (one_le_energyNorm h.nonempty))
    ((uniformExponent_ge_half_add hp).trans (sharpExponent_ge_uniform hp))
    (hfan.trans hlog) hcrit

end
end Erdos539Geometry
