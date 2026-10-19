/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelMaxWeights
import Erdos539.ScalarPositiveDifferenceCapacity

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- A strictly positive scalar output determines its target uniquely. -/
theorem scalarChannel_target_unique {S : Finset ℝ} (c a x : S) (ha : c.val < a.val)
    (he : scalarPositiveDifferenceChannel S c x = scalarPositiveDifferenceChannel S c a) : x = a := by
  have h := congrArg Subtype.val he
  change max (x.val - c.val) 0 = max (a.val - c.val) 0 at h
  rw [max_eq_left (show 0 ≤ a.val - c.val by linarith)] at h
  have hx : c.val < x.val := by
    by_contra hn
    rw [max_eq_right (by linarith)] at h
    linarith
  rw [max_eq_left (by linarith)] at h
  exact Subtype.ext (by linarith)

theorem scalarChannel_nonzero {S : Finset ℝ} (c a : S) (ha : c.val < a.val) :
    scalarPositiveDifferenceChannel S c a ≠ scalarPositiveDifferenceChannel S c c := by
  intro h
  have he := congrArg Subtype.val h
  change max (a.val - c.val) 0 = max (c.val - c.val) 0 at he
  simp only [sub_self, max_self] at he
  rw [max_eq_left (by linarith)] at he
  linarith

theorem scalarChannel_outputs {S : Finset ℝ} (c : S) :
    channelOutputs (scalarPositiveDifferenceChannel S) c =
      insert (scalarPositiveDifferenceChannel S c c)
        ((Finset.univ.filter (fun a : S ↦ c.val < a.val)).image (scalarPositiveDifferenceChannel S c)) := by
  ext z
  constructor
  · intro hz
    have hz' : ∃ a : S, scalarPositiveDifferenceChannel S c a = z := by
      simpa only [channelOutputs, Finset.mem_image, Finset.mem_univ, true_and] using hz
    obtain ⟨a, rfl⟩ := hz'
    by_cases ha : c.val < a.val
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)
    · have he : scalarPositiveDifferenceChannel S c a = scalarPositiveDifferenceChannel S c c := by
        apply Subtype.ext
        change max (a.val - c.val) 0 = max (c.val - c.val) 0
        rw [max_eq_right (by linarith)]
        simp
      exact Finset.mem_insert.mpr (Or.inl he)
  · intro hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · rw [hz]
      exact mem_channelOutputs _ c c
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
      exact mem_channelOutputs _ c a

theorem scalarChannel_max_positive {S : Finset ℝ} (g : S → ℝ) (hg : ∀ a, 0 < g a)
    (c a : S) (ha : c.val < a.val) :
    channelMaxWeight (scalarPositiveDifferenceChannel S) g c (scalarPositiveDifferenceChannel S c a) = g a := by
  obtain ⟨x, hx, he⟩ := (channelMaxWeight_spec (scalarPositiveDifferenceChannel S) g hg c
    (mem_channelOutputs _ c a)).1
  rw [scalarChannel_target_unique c a x ha hx] at he
  exact he

/-- The collapsed zero-output class is represented by any maximal weight
among targets below the anchor. -/
theorem scalarChannel_max_zero {S : Finset ℝ} (g : S → ℝ) (hg : ∀ a, 0 < g a)
    (c m : S) (hm : m.val ≤ c.val) (hmax : ∀ a : S, a.val ≤ c.val → g a ≤ g m) :
    channelMaxWeight (scalarPositiveDifferenceChannel S) g c (scalarPositiveDifferenceChannel S c c) = g m := by
  have hmc : scalarPositiveDifferenceChannel S c m = scalarPositiveDifferenceChannel S c c := by
    apply Subtype.ext
    change max (m.val - c.val) 0 = max (c.val - c.val) 0
    rw [max_eq_right (sub_nonpos.mpr hm)]
    simp
  have h := channelMaxWeight_spec (scalarPositiveDifferenceChannel S) g hg c (mem_channelOutputs _ c c)
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := h.1
    rw [he]
    have hv := congrArg Subtype.val hx
    change max (x.val - c.val) 0 = max (c.val - c.val) 0 at hv
    have hxc : x.val ≤ c.val := by
      simp only [sub_self, max_self] at hv
      have hl := le_max_left (x.val - c.val) 0
      linarith
    exact hmax x hxc
  · exact h.2 m hmc

/-- Exact scalar row partition: one collapsed lower class plus the
individual weights of every target strictly above the anchor. -/
theorem scalarChannel_weightSum {S : Finset ℝ} (g : S → ℝ) (hg : ∀ a, 0 < g a)
    (c m : S) (hm : m.val ≤ c.val) (hmax : ∀ a : S, a.val ≤ c.val → g a ≤ g m) :
    channelWeightSum (scalarPositiveDifferenceChannel S) g c =
      g m + ∑ a ∈ Finset.univ.filter (fun a : S ↦ c.val < a.val), g a := by
  have hT : channelWeightSum (scalarPositiveDifferenceChannel S) g c =
      ∑ z ∈ channelOutputs (scalarPositiveDifferenceChannel S) c,
        channelMaxWeight (scalarPositiveDifferenceChannel S) g c z := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz
    exact channelMaxWeight_eq_zero _ g c hz
  rw [hT, scalarChannel_outputs]
  have hn : scalarPositiveDifferenceChannel S c c ∉
      (Finset.univ.filter (fun a : S ↦ c.val < a.val)).image (scalarPositiveDifferenceChannel S c) := by
    intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    exact scalarChannel_nonzero c a (Finset.mem_filter.mp ha).2 he
  rw [Finset.sum_insert hn, scalarChannel_max_zero g hg c m hm hmax]
  congr 1
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    exact scalarChannel_max_positive g hg c a (Finset.mem_filter.mp ha).2
  · intro a ha x _ he
    exact (scalarChannel_target_unique c a x (Finset.mem_filter.mp ha).2 he.symm).symm

end
end Erdos539Geometry
