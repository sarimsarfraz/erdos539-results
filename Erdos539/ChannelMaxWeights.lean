/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelWeakDuality

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

/-- The maximum positive weight in an actual output class, and zero at
unavailable outputs. Its maximum characterization is proved below. -/
def channelMaxWeight (channel : α → α → β) (g : α → ℝ) (a : α) (z : β) : ℝ :=
  channelReference channel (fun x ↦ -Real.log (g x)) a z

def channelWeightSum (channel : α → α → β) (g : α → ℝ) (a : α) : ℝ :=
  ∑ z, channelMaxWeight channel g a z

/-- The literal ratio Tg/g from the energy--fan norm formulation. -/
def channelWeightRatio (channel : α → α → β) (g : α → ℝ) (a : α) : ℝ :=
  channelWeightSum channel g a / g a

omit [Fintype β] in
theorem channelMaxWeight_eq_zero (channel : α → α → β) (g : α → ℝ) (a : α) {z : β}
    (hz : z ∉ channelOutputs channel a) : channelMaxWeight channel g a z = 0 := by
  simp [channelMaxWeight, channelReference, hz]

omit [Fintype β] in
theorem channelMaxWeight_spec (channel : α → α → β) (g : α → ℝ)
    (hg : ∀ x, 0 < g x) (a : α) {z : β} (hz : z ∈ channelOutputs channel a) :
    (∃ x, channel a x = z ∧ channelMaxWeight channel g a z = g x) ∧
    ∀ x, channel a x = z → g x ≤ channelMaxWeight channel g a z := by
  let r := minPotentialRepresentative channel (fun x ↦ -Real.log (g x)) a z
  have hr := minPotentialRepresentative_spec channel (fun x ↦ -Real.log (g x)) a hz
  have he : channelMaxWeight channel g a z = g r := by
    simp [channelMaxWeight, channelReference, hz, r, Real.exp_log (hg _)]
  refine ⟨⟨r, hr.1, he⟩, ?_⟩
  intro x hx
  rw [he]
  have h := hr.2 x hx
  have hh : Real.log (g x) ≤ Real.log (g r) := by linarith
  exact (Real.log_le_log_iff (hg x) (hg r)).mp hh

theorem channelWeightRatio_pos (channel : α → α → β) (g : α → ℝ)
    (hg : ∀ x, 0 < g x) (a : α) : 0 < channelWeightRatio channel g a :=
  div_pos (channelPartition_pos channel (fun x ↦ -Real.log (g x)) a) (hg a)

theorem channelDualValue_eq_weightRatio (ν : α → ℝ) (channel : α → α → β)
    (g : α → ℝ) (hg : ∀ x, 0 < g x) :
    channelDualValue ν channel (fun x ↦ -Real.log (g x)) =
      ∑ a, ν a * Real.log (channelWeightRatio channel g a) := by
  unfold channelDualValue
  apply Finset.sum_congr rfl
  intro a _
  change ν a * (-Real.log (g a) + Real.log (channelPartition channel (fun x ↦ -Real.log (g x)) a)) =
    ν a * Real.log (channelPartition channel (fun x ↦ -Real.log (g x)) a / g a)
  rw [Real.log_div (channelPartition_pos channel (fun x ↦ -Real.log (g x)) a).ne' (hg a).ne']
  ring

theorem stationaryCapacity_le_weightRatio (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a)
    (hs : ∑ a, ν a = 1) (channel : α → α → β) (g : α → ℝ) (hg : ∀ x, 0 < g x) :
    stationaryCapacity ν channel ≤ ∑ a, ν a * Real.log (channelWeightRatio channel g a) := by
  rw [← channelDualValue_eq_weightRatio ν channel g hg]
  exact stationaryCapacity_le_channelDualValue ν hν hs channel _

/-- The weight form of the finite dual is arbitrarily close, even when
the prescribed endpoint law has zero atoms. -/
theorem weightRatio_approximate (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a)
    (hs : ∑ a, ν a = 1) (channel : α → α → β) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → ℝ, (∀ x, 0 < g x) ∧
      (∑ a, ν a * Real.log (channelWeightRatio channel g a)) < stationaryCapacity ν channel + ε := by
  obtain ⟨t, ht⟩ := channelDualValue_approximate ν hν hs channel hε
  let g : α → ℝ := fun x ↦ Real.exp (-t x)
  have hg : ∀ x, 0 < g x := fun x ↦ Real.exp_pos _
  refine ⟨g, hg, ?_⟩
  rw [← channelDualValue_eq_weightRatio ν channel g hg]
  have he : (fun x ↦ -Real.log (g x)) = t := by funext x; simp [g]
  rw [he]
  exact ht

end
end Erdos539Geometry
