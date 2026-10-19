/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanPowerSum
import Erdos539.FinitePositiveReference
import Erdos539.StationaryEntropyDuality

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G β : Type*} [AddCommGroup G] [DecidableEq G] [Fintype β]

/-- A weighted energy inequality on the original finite support. -/
def FanNormBound (S : Finset G) (channel : S → S → β) (p C : ℝ) : Prop :=
  ∀ f g : S → ℝ, (∀ a, 0 < f a) → (∀ a, 0 < g a) →
    weightedGibbsPartition S f ≤ C * (fanPowerSum channel f g p) ^ (4 / p)

/-- The corresponding bound for every stationary endpoint law, including
laws with zero atoms. -/
def FanEntropyBound (S : Finset G) (channel : S → S → β) (p C : ℝ) : Prop :=
  ∀ ν : S → ℝ, (∀ a, 0 ≤ ν a) → (∑ a, ν a = 1) →
    stationaryAdditiveEntropy S ν ≤ 2 * stationaryCapacity ν channel +
      (4 / p) * finiteEntropy ν + Real.log C

theorem FanEntropyBound.to_norm {S : Finset G} (hS : S.Nonempty)
    {channel : S → S → β} {p C : ℝ} (hp : 0 < p) (hC : 0 < C)
    (h : FanEntropyBound S channel p C) : FanNormBound S channel p C := by
  letI : Nonempty S := hS.coe_sort
  intro f g hf hg
  let ν := weightedGibbsEndpoint S f
  have hZ := weightedGibbsPartition_pos hS hf
  have hν : ∀ a, 0 ≤ ν a := weightedGibbsEndpoint_nonneg (fun a ↦ (hf a).le)
  have hs : ∑ a, ν a = 1 := weightedGibbsEndpoint_sum hZ.ne'
  have he : stationaryAdditiveEntropy S ν = Real.log (weightedGibbsPartition S f) -
      4 * ∑ a, ν a * Real.log (f a) := by
    rw [stationaryAdditiveEntropy_eq_of_maximal _ (weightedGibbs_entropy_maximal hf hZ)]
    exact weightedGibbs_entropy hf hZ
  have hA := h ν hν hs
  have hF := stationaryCapacity_le_weightRatio ν hν hs channel g hg
  have hv := fanPowerSum_entropy_bound ν hν hs channel f g hf hg hp
  have hW := fanPowerSum_pos channel f g hf hg p
  apply (Real.log_le_log_iff hZ (mul_pos hC (Real.rpow_pos_of_pos hW _))).mp
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hW _).ne', Real.log_rpow hW]
  rw [he] at hA
  linarith

theorem FanNormBound.to_entropy {S : Finset G} (hS : S.Nonempty)
    {channel : S → S → β} {p C : ℝ} (hp : 0 < p) (hC : 0 < C)
    (h : FanNormBound S channel p C) : FanEntropyBound S channel p C := by
  letI : Nonempty S := hS.coe_sort
  intro ν hν hs
  apply le_of_forall_pos_le_add
  intro ε hε
  let k := 4 / p
  have hk : 0 < k := div_pos (by norm_num) hp
  obtain ⟨g, hg, hF⟩ := weightRatio_approximate ν hν hs channel
    (show 0 < ε / 4 by positivity)
  obtain ⟨w, hw, hWlog, hcross⟩ := finite_positive_reference ν hν hs
    (show 0 < ε / (2 * k) by positivity)
  let f : S → ℝ := fun a ↦ (w a) ^ (1 / p) / Real.sqrt (channelWeightRatio channel g a)
  obtain ⟨hf, hsum, hflog⟩ := fanPowerSum_test channel g w hg hw hp
  have hZ := weightedGibbsPartition_pos hS hf
  have hN := h f g hf hg
  have hW := fanPowerSum_pos channel f g hf hg p
  have hlog := Real.log_le_log hZ hN
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hW _).ne', Real.log_rpow hW, hsum] at hlog
  have hA := stationaryAdditiveEntropy_le_partition hS hν hs hf
  have he : 4 * (∑ a, ν a * Real.log (f a)) =
      k * (∑ a, ν a * Real.log (w a)) -
        2 * (∑ a, ν a * Real.log (channelWeightRatio channel g a)) := by
    simp only [f, hflog, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [k]
    ring
  rw [he] at hA
  have hcross' := mul_le_mul_of_nonneg_left hcross hk.le
  have hWlog' := mul_le_mul_of_nonneg_left hWlog hk.le
  have hcancel : k * (ε / (2 * k)) = ε / 2 := by field_simp
  rw [hcancel] at hWlog'
  change Real.log (weightedGibbsPartition S f) ≤ Real.log C + k * Real.log (∑ a, w a) at hlog
  change stationaryAdditiveEntropy S ν ≤ 2 * stationaryCapacity ν channel + k * finiteEntropy ν + Real.log C + ε
  linarith

/-- Exact norm/entropy equivalence, proved on each fixed support and
channel. Consequently it also holds uniformly over all finite supports. -/
theorem fanNormBound_iff_entropy {S : Finset G} (hS : S.Nonempty)
    (channel : S → S → β) {p C : ℝ} (hp : 0 < p) (hC : 0 < C) :
    FanNormBound S channel p C ↔ FanEntropyBound S channel p C :=
  ⟨fun h ↦ h.to_entropy hS hp hC, fun h ↦ h.to_norm hS hp hC⟩

end
end Erdos539Geometry
