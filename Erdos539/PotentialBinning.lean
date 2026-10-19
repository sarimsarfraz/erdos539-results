/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelPotentialShift
import Erdos539.FiniteGeometricEntropy
import Mathlib.Algebra.Order.Floor.Ring

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- A finite range containing all original potential-bin labels. -/
def potentialBinCount {α : Type*} [Fintype α] (t : α → ℝ) : ℕ :=
  (Finset.univ.sup fun a ↦ ⌊t a⌋₊) + 1

def potentialBin {α : Type*} [Fintype α] (t : α → ℝ) (a : α) : Fin (potentialBinCount t) :=
  ⟨⌊t a⌋₊, Nat.lt_succ_of_le (Finset.le_sup (f := fun a ↦ ⌊t a⌋₊) (Finset.mem_univ a))⟩

theorem potentialBin_le {α : Type*} [Fintype α]
    (t : α → ℝ) (ht : ∀ a, 0 ≤ t a) (a : α) :
    ((potentialBin t a).val : ℝ) ≤ t a := Nat.floor_le (ht a)

theorem potentialBin_width {α : Type*} [Fintype α]
    (t : α → ℝ) (ht : ∀ a, 0 ≤ t a) (a x : α)
    (hbin : potentialBin t x = potentialBin t a) : t x ≤ t a + 1 := by
  have he : ⌊t x⌋₊ = ⌊t a⌋₊ := congrArg Fin.val hbin
  have hx := Nat.lt_floor_add_one (t x)
  rw [he] at hx
  have ha := Nat.floor_le (ht a)
  linarith

/-- The entropy of the literal floor labels is controlled by the
normalized dual value. -/
theorem potentialBin_entropy_le {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (t : α → ℝ) (ht : ∀ a, 0 ≤ t a)
    {m : α} (hm : t m = 0) :
    finiteEntropy (finitePush ν (potentialBin t)) ≤ Real.log (channelDualValue ν channel t + 1) + 1 := by
  have hmean := potential_mean_le_channelDualValue ν hν channel t ht hm
  have hnon : 0 ≤ channelDualValue ν channel t :=
    (Finset.sum_nonneg (fun a _ ↦ mul_nonneg (hν a) (ht a))).trans hmean
  apply finiteEntropy_nat_mean_le _ (finitePush_nonneg ν _ hν)
    (by rw [finitePush_sum, hs]) hnon
  rw [finitePush_expectation]
  apply le_trans _ hmean
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (potentialBin_le t ht a) (hν a)

end
end Erdos539Geometry
