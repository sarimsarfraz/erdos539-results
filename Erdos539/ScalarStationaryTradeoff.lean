/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarPotentialRanks
import Erdos539.PotentialBinning
import Erdos539.FiniteBinRankEntropy
import Erdos539.FiniteCouplingEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- The rank and floor-bin estimates for every normalized dual potential. -/
theorem normalized_scalar_dual_entropy_bound {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (hinj : UpperConeInjective channel)
    (t : α → ℝ) (ht : ∀ a, 0 ≤ t a) {m : α} (hm : t m = 0)
    {s : ℝ} (hs1 : 1 < s) :
    finiteEntropy ν ≤ Real.log (channelDualValue ν channel t + 1) + 1 +
      s * (channelDualValue ν channel t + 1) + Real.log (1 + 1 / (s - 1)) := by
  have hr := finiteEntropy_le_bin_rank ν hν hs (potentialBin t)
    (binRankIndex (potentialBin t)) (bin_rank_injective (potentialBin t)) hs1
  have hbin := potentialBin_entropy_le ν hν hs channel t ht hm
  have hrank := bin_rank_log_expectation_le ν hν hs channel hinj t (potentialBin t)
    (potentialBin_width t ht)
  have hmul := mul_le_mul_of_nonneg_left hrank (show 0 ≤ s by linarith)
  linarith

/-- A convenient logarithm estimate used to pass from approximate dual
potentials to the exact stationary capacity without a minimizer premise. -/
theorem log_add_increment_le {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    Real.log (x + ε + 1) ≤ Real.log (x + 1) + ε := by
  have hx1 : 0 < x + 1 := by linarith
  have hxε : 0 < x + ε + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hxε hx1)
  rw [Real.log_div hxε.ne' hx1.ne'] at h
  have hratio : (x + ε + 1) / (x + 1) ≤ 1 + ε := by
    apply (div_le_iff₀ hx1).mpr
    nlinarith
  linarith

/-- The finite scalar stationary tradeoff for every exponent s > 1.
This is unconditional for any finite ordered channel injective above its
anchor, and uses the actual stationary optimization. -/
theorem scalar_stationary_entropy_tradeoff {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (hinj : UpperConeInjective channel)
    {s : ℝ} (hs1 : 1 < s) :
    finiteEntropy ν ≤ Real.log (stationaryCapacity ν channel + 1) + 1 +
      s * (stationaryCapacity ν channel + 1) + Real.log (1 + 1 / (s - 1)) := by
  let F := stationaryCapacity ν channel
  let B := Real.log (F + 1) + 1 + s * (F + 1) + Real.log (1 + 1 / (s - 1))
  have hF : 0 ≤ F := (stationaryCapacity_bounds ν hν hs channel).1
  have happ : ∀ ε : ℝ, 0 < ε → finiteEntropy ν ≤ B + (s + 1) * ε := by
    intro ε hε
    obtain ⟨t, ht, ⟨m, hm⟩, happrox⟩ := channelDualValue_approximate_normalized ν hν hs channel hε
    have he := normalized_scalar_dual_entropy_bound ν hν hs channel hinj t ht hm hs1
    have hL := potential_mean_le_channelDualValue ν hν channel t ht hm
    have hL0 : 0 ≤ channelDualValue ν channel t :=
      (Finset.sum_nonneg (fun a _ ↦ mul_nonneg (hν a) (ht a))).trans hL
    have hl := Real.log_le_log (show 0 < channelDualValue ν channel t + 1 by linarith)
      (show channelDualValue ν channel t + 1 ≤ F + ε + 1 by linarith)
    have hlog := log_add_increment_le hF hε.le
    have hmul := mul_le_mul_of_nonneg_left (show channelDualValue ν channel t + 1 ≤ F + ε + 1 by linarith)
      (show 0 ≤ s by linarith)
    dsimp [B]
    linarith
  change finiteEntropy ν ≤ B
  by_contra hn
  have hgap : 0 < finiteEntropy ν - B := sub_pos.mpr (lt_of_not_ge hn)
  have hden : 0 < 2 * (s + 1) := by linarith
  have h := happ ((finiteEntropy ν - B) / (2 * (s + 1))) (div_pos hgap hden)
  have he := div_mul_cancel₀ (finiteEntropy ν - B) hden.ne'
  nlinarith

end
end Erdos539Geometry
