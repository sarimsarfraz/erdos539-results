/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteEntropyMixtures
import Erdos539.FinitePushProducts
import Mathlib.Data.Finset.Max

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- The literal set of outputs available at one fixed endpoint. -/
def channelOutputs {α β : Type*} [Fintype α] (channel : α → α → β) (a : α) : Finset β :=
  Finset.univ.image (channel a)

theorem mem_channelOutputs {α β : Type*} [Fintype α]
    (channel : α → α → β) (a x : α) : channel a x ∈ channelOutputs channel a :=
  Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

/-- Select a minimum-potential representative of a nonempty output class.
The arbitrary fallback is only used at unavailable outputs. -/
def minPotentialRepresentative {α β : Type*} [Fintype α]
    (channel : α → α → β) (t : α → ℝ) (a : α) (z : β) : α :=
  if h : (Finset.univ.filter (fun x ↦ channel a x = z)).Nonempty then
    (Finset.exists_min_image _ t h).choose else a

theorem minPotentialRepresentative_spec {α β : Type*} [Fintype α]
    (channel : α → α → β) (t : α → ℝ) (a : α) {z : β}
    (hz : z ∈ channelOutputs channel a) :
    channel a (minPotentialRepresentative channel t a z) = z ∧
      ∀ x, channel a x = z → t (minPotentialRepresentative channel t a z) ≤ t x := by
  have hn : (Finset.univ.filter (fun x ↦ channel a x = z)).Nonempty := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  rw [minPotentialRepresentative, dif_pos hn]
  obtain ⟨hm, hmin⟩ := (Finset.exists_min_image _ t hn).choose_spec
  refine ⟨(Finset.mem_filter.mp hm).2, ?_⟩
  intro x hx
  exact hmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

/-- Exponential reference weight on actual output classes. -/
def channelReference {α β : Type*} [Fintype α]
    (channel : α → α → β) (t : α → ℝ) (a : α) (z : β) : ℝ :=
  if z ∈ channelOutputs channel a then
    Real.exp (-t (minPotentialRepresentative channel t a z)) else 0

def channelPartition {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (a : α) : ℝ :=
  ∑ z, channelReference channel t a z

theorem channelReference_nonneg {α β : Type*} [Fintype α]
    (channel : α → α → β) (t : α → ℝ) (a : α) (z : β) :
    0 ≤ channelReference channel t a z := by
  dsimp [channelReference]
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

theorem channelPartition_pos {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (a : α) :
    0 < channelPartition channel t a := by
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := channelReference channel t a) (fun z _ ↦ channelReference_nonneg channel t a z)
    (Finset.mem_univ (channel a a))
  apply lt_of_lt_of_le _ hle
  rw [channelReference, if_pos (mem_channelOutputs channel a a)]
  exact Real.exp_pos _

def channelSoftmax {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (a : α) (z : β) : ℝ :=
  channelReference channel t a z / channelPartition channel t a

theorem channelSoftmax_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (a : α) (z : β) :
    0 ≤ channelSoftmax channel t a z :=
  div_nonneg (channelReference_nonneg channel t a z) (channelPartition_pos channel t a).le

theorem channelSoftmax_sum {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (a : α) :
    ∑ z, channelSoftmax channel t a z = 1 := by
  simp only [channelSoftmax, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (channelPartition_pos channel t a).ne'

theorem channelSoftmax_support {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (a : α) {z : β}
    (hz : channelSoftmax channel t a z ≠ 0) : z ∈ channelOutputs channel a := by
  by_contra hn
  apply hz
  simp [channelSoftmax, channelReference, hn]

/-- Each output row exactly attains its Gibbs bound at minimum-potential
representatives, including unavailable output labels of weight zero. -/
theorem channelSoftmax_entropy {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (t : α → ℝ) (a : α) :
    finiteEntropy (channelSoftmax channel t a) -
      (∑ z, channelSoftmax channel t a z * t (minPotentialRepresentative channel t a z)) =
      Real.log (channelPartition channel t a) := by
  have he := finiteEntropy_normalize (channelReference channel t a) (channelPartition_pos channel t a)
  change finiteEntropy (channelSoftmax channel t a) = Real.log (channelPartition channel t a) -
    ∑ z, channelSoftmax channel t a z * Real.log (channelReference channel t a z) at he
  have hpoint (z : β) : channelSoftmax channel t a z * Real.log (channelReference channel t a z) =
      -(channelSoftmax channel t a z * t (minPotentialRepresentative channel t a z)) := by
    by_cases hz : channelSoftmax channel t a z = 0
    · simp [hz]
    · rw [channelReference, if_pos (channelSoftmax_support channel t a hz), Real.log_exp]
      ring
  simp only [hpoint, Finset.sum_neg_distrib] at he
  linarith

/-- The finite dual expression before normalization of its potential. -/
def channelDualValue {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (channel : α → α → β) (t : α → ℝ) : ℝ :=
  ∑ a, ν a * (t a + Real.log (channelPartition channel t a))

end
end Erdos539Geometry
