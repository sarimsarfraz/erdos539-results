/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelWeakDuality

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem minPotentialRepresentative_shift_value {α β : Type*} [Fintype α]
    (channel : α → α → β) (t : α → ℝ) (c : ℝ) (a : α) {z : β}
    (hz : z ∈ channelOutputs channel a) :
    t (minPotentialRepresentative channel (fun x ↦ t x - c) a z) =
      t (minPotentialRepresentative channel t a z) := by
  obtain ⟨h1, hmin1⟩ := minPotentialRepresentative_spec channel t a hz
  obtain ⟨h2, hmin2⟩ := minPotentialRepresentative_spec channel (fun x ↦ t x - c) a hz
  have hle1 := hmin1 _ h2
  have hle2 := hmin2 _ h1
  linarith

theorem channelReference_shift {α β : Type*} [Fintype α]
    (channel : α → α → β) (t : α → ℝ) (c : ℝ) (a : α) (z : β) :
    channelReference channel (fun x ↦ t x - c) a z =
      Real.exp c * channelReference channel t a z := by
  by_cases hz : z ∈ channelOutputs channel a
  · simp only [channelReference, if_pos hz]
    rw [minPotentialRepresentative_shift_value channel t c a hz]
    rw [neg_sub, sub_eq_add_neg, Real.exp_add]
  · simp [channelReference, hz]

theorem channelPartition_shift {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (c : ℝ) (a : α) :
    channelPartition channel (fun x ↦ t x - c) a = Real.exp c * channelPartition channel t a := by
  simp only [channelPartition, channelReference_shift, Finset.mul_sum]

theorem channelDualValue_shift {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (channel : α → α → β) (t : α → ℝ) (c : ℝ) :
    channelDualValue ν channel (fun x ↦ t x - c) = channelDualValue ν channel t := by
  apply Finset.sum_congr rfl
  intro a _
  rw [channelPartition_shift, Real.log_mul (Real.exp_ne_zero c) (channelPartition_pos channel t a).ne', Real.log_exp]
  ring

/-- Any normalized nonnegative potential gives every row partition a
term of weight at least one, even if its minimum has zero law-mass. -/
theorem one_le_channelPartition_of_min_zero {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (ht : ∀ x, 0 ≤ t x)
    {m : α} (hm : t m = 0) (a : α) : 1 ≤ channelPartition channel t a := by
  have hmin := (minPotentialRepresentative_spec channel t a (mem_channelOutputs channel a m)).2 m rfl
  have he : t (minPotentialRepresentative channel t a (channel a m)) = 0 := by
    have hnon := ht (minPotentialRepresentative channel t a (channel a m))
    rw [hm] at hmin
    exact le_antisymm hmin hnon
  have hle := Finset.single_le_sum (s := Finset.univ) (f := channelReference channel t a)
    (fun z _ ↦ channelReference_nonneg channel t a z) (Finset.mem_univ (channel a m))
  simpa only [channelReference, if_pos (mem_channelOutputs channel a m), he, neg_zero, Real.exp_zero] using hle

theorem potential_mean_le_channelDualValue {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (channel : α → α → β)
    (t : α → ℝ) (ht : ∀ x, 0 ≤ t x) {m : α} (hm : t m = 0) :
    (∑ a, ν a * t a) ≤ channelDualValue ν channel t := by
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hν a)
  have hlog := Real.log_nonneg (one_le_channelPartition_of_min_zero channel t ht hm a)
  linarith

/-- Dual approximation can always use a nonnegative potential with
minimum exactly zero, without requiring positive probabilities. -/
theorem channelDualValue_approximate_normalized {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : α → ℝ, (∀ a, 0 ≤ t a) ∧ (∃ m, t m = 0) ∧
      channelDualValue ν channel t < stationaryCapacity ν channel + ε := by
  have hn : (Finset.univ : Finset α).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at hs
    norm_num at hs
  obtain ⟨t, ht⟩ := channelDualValue_approximate ν hν hs channel hε
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ t hn
  refine ⟨fun a ↦ t a - t m, fun a ↦ sub_nonneg.mpr (hm a (Finset.mem_univ _)),
    ⟨m, sub_self _⟩, ?_⟩
  rw [channelDualValue_shift]
  exact ht

end
end Erdos539Geometry
