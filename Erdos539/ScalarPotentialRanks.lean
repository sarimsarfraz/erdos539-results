/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarBinRanks

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- A scalar channel only needs injectivity above each anchor for the
rank argument. The positive-part difference channel has this property. -/
def UpperConeInjective {α β : Type*} [Preorder α] (channel : α → α → β) : Prop :=
  ∀ a x y, a ≤ x → a ≤ y → channel a x = channel a y → x = y

/-- A unit-width potential bin contributes its reverse rank to the row
partition. Both the order and all ties are handled in the original support. -/
theorem binReverseRank_log_le_potential_row {α β γ : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    (channel : α → α → β) (hinj : UpperConeInjective channel)
    (t : α → ℝ) (bin : α → γ)
    (hwidth : ∀ a x, bin x = bin a → t x ≤ t a + 1) (a : α) :
    Real.log (binReverseRank bin a) ≤ t a + Real.log (channelPartition channel t a) + 1 := by
  let U := binUpperSet bin a
  have hmap : Set.InjOn (channel a) U := by
    intro x hx y hy he
    exact hinj a x y (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2 he
  have hsum : (binReverseRank bin a : ℝ) * Real.exp (-(t a + 1)) ≤ channelPartition channel t a := by
    calc
      _ = ∑ x ∈ U, Real.exp (-(t a + 1)) := by simp [U, binReverseRank]
      _ ≤ ∑ x ∈ U, channelReference channel t a (channel a x) := by
        apply Finset.sum_le_sum
        intro x hx
        have hxbin := (Finset.mem_filter.mp hx).2.1
        have hmin := (minPotentialRepresentative_spec channel t a (mem_channelOutputs channel a x)).2 x rfl
        rw [channelReference, if_pos (mem_channelOutputs channel a x)]
        apply Real.exp_le_exp.mpr
        have hw := hwidth a x hxbin
        linarith
      _ = ∑ z ∈ U.image (channel a), channelReference channel t a z := (Finset.sum_image hmap).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ ↦ channelReference_nonneg channel t a z)
  have hr : (0 : ℝ) < binReverseRank bin a := by exact_mod_cast binReverseRank_pos bin a
  have hl := Real.log_le_log (mul_pos hr (Real.exp_pos _)) hsum
  rw [Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  linarith

theorem bin_rank_log_expectation_le {α β γ : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (hinj : UpperConeInjective channel)
    (t : α → ℝ) (bin : α → γ)
    (hwidth : ∀ a x, bin x = bin a → t x ≤ t a + 1) :
    (∑ a, ν a * Real.log ((binRankIndex bin a).val + 1)) ≤ channelDualValue ν channel t + 1 := by
  have hpoint (a : α) : Real.log ((binRankIndex bin a).val + 1) ≤
      t a + Real.log (channelPartition channel t a) + 1 := by
    have he : ((binRankIndex bin a).val : ℝ) + 1 = binReverseRank bin a := by
      exact_mod_cast binRankIndex_add_one bin a
    rw [he]
    exact binReverseRank_log_le_potential_row channel hinj t bin hwidth a
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ ↦ mul_le_mul_of_nonneg_left (hpoint a) (hν a))
  simpa only [mul_add, mul_one, Finset.sum_add_distrib, hs, channelDualValue] using hsum

end
end Erdos539Geometry
