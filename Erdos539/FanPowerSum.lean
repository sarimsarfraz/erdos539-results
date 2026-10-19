/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelMaxWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

/-- The pth power of the counting-measure norm of f sqrt(Tg/g). -/
def fanPowerSum (channel : α → α → β) (f g : α → ℝ) (p : ℝ) : ℝ :=
  ∑ a, (f a * Real.sqrt (channelWeightRatio channel g a)) ^ p

theorem fanPowerSum_pos [Nonempty α] (channel : α → α → β) (f g : α → ℝ)
    (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) (p : ℝ) : 0 < fanPowerSum channel f g p := by
  apply Finset.sum_pos
  · intro a _
    exact Real.rpow_pos_of_pos (mul_pos (hf a) (Real.sqrt_pos.2 (channelWeightRatio_pos channel g hg a))) p
  · exact Finset.univ_nonempty

theorem fanPowerSum_log_weight (channel : α → α → β) (f g : α → ℝ)
    (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) (p : ℝ) (a : α) :
    Real.log ((f a * Real.sqrt (channelWeightRatio channel g a)) ^ p) =
      p * (Real.log (f a) + Real.log (channelWeightRatio channel g a) / 2) := by
  have hR := channelWeightRatio_pos channel g hg a
  rw [Real.log_rpow (mul_pos (hf a) (Real.sqrt_pos.2 hR)),
    Real.log_mul (hf a).ne' (Real.sqrt_pos.2 hR).ne', Real.log_sqrt hR.le]

/-- The entropy variational estimate for the actual weighted power sum. -/
theorem fanPowerSum_entropy_bound [Nonempty α] (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a)
    (hs : ∑ a, ν a = 1) (channel : α → α → β) (f g : α → ℝ)
    (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) {p : ℝ} (hp : 0 < p) :
    (4 / p) * finiteEntropy ν + 4 * (∑ a, ν a * Real.log (f a)) +
      2 * (∑ a, ν a * Real.log (channelWeightRatio channel g a)) ≤
      (4 / p) * Real.log (fanPowerSum channel f g p) := by
  let w : α → ℝ := fun a ↦ (f a * Real.sqrt (channelWeightRatio channel g a)) ^ p
  have hw : ∀ a, 0 < w a := fun a ↦ Real.rpow_pos_of_pos
    (mul_pos (hf a) (Real.sqrt_pos.2 (channelWeightRatio_pos channel g hg a))) p
  have h := finiteEntropy_le_log_partition ν w hν hs (fun a ↦ (hw a).le)
    (fanPowerSum_pos channel f g hf hg p) (fun a _ ↦ hw a)
  have he : (∑ a, ν a * Real.log (w a)) =
      p * (∑ a, ν a * Real.log (f a)) + (p / 2) * (∑ a, ν a * Real.log (channelWeightRatio channel g a)) := by
    simp only [w, fanPowerSum_log_weight channel f g hf hg, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he] at h
  change finiteEntropy ν ≤ Real.log (fanPowerSum channel f g p) - _ at h
  calc
    _ = (4 / p) * (finiteEntropy ν + p * (∑ a, ν a * Real.log (f a)) +
        (p / 2) * (∑ a, ν a * Real.log (channelWeightRatio channel g a))) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Positive test weights realize any positive reference w exactly. -/
theorem fanPowerSum_test (channel : α → α → β) (g w : α → ℝ)
    (hg : ∀ a, 0 < g a) (hw : ∀ a, 0 < w a) {p : ℝ} (hp : 0 < p) :
    let f : α → ℝ := fun a ↦ (w a) ^ (1 / p) / Real.sqrt (channelWeightRatio channel g a)
    (∀ a, 0 < f a) ∧ fanPowerSum channel f g p = ∑ a, w a ∧
      ∀ a, Real.log (f a) = (1 / p) * Real.log (w a) - Real.log (channelWeightRatio channel g a) / 2 := by
  dsimp only
  have hsqrt (a : α) : 0 < Real.sqrt (channelWeightRatio channel g a) :=
    Real.sqrt_pos.2 (channelWeightRatio_pos channel g hg a)
  refine ⟨fun a ↦ div_pos (Real.rpow_pos_of_pos (hw a) _) (hsqrt a), ?_, ?_⟩
  · unfold fanPowerSum
    apply Finset.sum_congr rfl
    intro a _
    rw [div_mul_cancel₀ _ (hsqrt a).ne', ← Real.rpow_mul (hw a).le,
      div_mul_cancel₀ _ hp.ne', Real.rpow_one]
  · intro a
    rw [Real.log_div (Real.rpow_pos_of_pos (hw a) _).ne' (hsqrt a).ne',
      Real.log_rpow (hw a), Real.log_sqrt (channelWeightRatio_pos channel g hg a).le]

end
end Erdos539Geometry
