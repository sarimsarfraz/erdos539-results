/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteDataProcessing
import Erdos539.FinitePushProducts

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Product of the two actual marginals of a finite joint weight. -/
def pairMarginalReference {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (z : α × β) : ℝ :=
  finitePush p Prod.fst z.1 * finitePush p Prod.snd z.2

theorem pairMarginalReference_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) (z : α × β) :
    0 ≤ pairMarginalReference p z :=
  mul_nonneg (finitePush_nonneg p Prod.fst hp z.1) (finitePush_nonneg p Prod.snd hp z.2)

theorem pairMarginalReference_pos {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) (z : α × β) (hz : p z ≠ 0) :
    0 < pairMarginalReference p z := by
  have hpos := lt_of_le_of_ne (hp z) (Ne.symm hz)
  exact mul_pos (hpos.trans_le (le_finitePush p Prod.fst hp z))
    (hpos.trans_le (le_finitePush p Prod.snd hp z))

theorem finiteRelEntropy_pairMarginalReference {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteRelEntropy p (pairMarginalReference p) = finiteEntropy (finitePush p Prod.fst) +
      finiteEntropy (finitePush p Prod.snd) - finiteEntropy p := by
  have hlog (z : α × β) : p z * Real.log (pairMarginalReference p z) = p z *
      (Real.log (finitePush p Prod.fst z.1) + Real.log (finitePush p Prod.snd z.2)) := by
    by_cases hz : p z = 0
    · simp [hz]
    · have hpos := lt_of_le_of_ne (hp z) (Ne.symm hz)
      rw [pairMarginalReference, Real.log_mul
        (hpos.trans_le (le_finitePush p Prod.fst hp z)).ne'
        (hpos.trans_le (le_finitePush p Prod.snd hp z)).ne']
  have hfst := finitePush_expectation p Prod.fst (fun a ↦ Real.log (finitePush p Prod.fst a))
  have hsnd := finitePush_expectation p Prod.snd (fun b ↦ Real.log (finitePush p Prod.snd b))
  simp only [finiteRelEntropy, mul_sub, Finset.sum_sub_distrib, hlog, mul_add, Finset.sum_add_distrib]
  rw [← hfst, ← hsnd]
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

def mapSecond {α β γ : Type*} (f : β → γ) (z : α × β) : α × γ := (z.1, f z.2)

theorem finitePush_product_mapSecond {α β γ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (f : β → γ) :
    finitePush (fun z : α × β ↦ p z.1 * q z.2) (mapSecond f) =
      fun z : α × γ ↦ p z.1 * finitePush q f z.2 := by
  funext z
  obtain ⟨u, v⟩ := z
  rw [finitePush, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single u]
  · simp only [mapSecond, Prod.mk.injEq, true_and, finitePush, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [mapSecond, ha]
  · simp

theorem finitePush_mapSecond_fst {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : β → γ) :
    finitePush (finitePush p (mapSecond f)) Prod.fst = finitePush p Prod.fst := by
  rw [finitePush_comp]
  rfl

theorem finitePush_mapSecond_snd {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : β → γ) :
    finitePush (finitePush p (mapSecond f)) Prod.snd = finitePush (finitePush p Prod.snd) f := by
  rw [finitePush_comp, finitePush_comp]
  rfl

theorem finitePush_pairMarginalReference {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : β → γ) :
    finitePush (pairMarginalReference p) (mapSecond f) = pairMarginalReference (finitePush p (mapSecond f)) := by
  unfold pairMarginalReference
  rw [finitePush_product_mapSecond, finitePush_mapSecond_fst, finitePush_mapSecond_snd]

/-- Conditioning on a deterministic function of the label can only
increase conditional entropy. This even holds for unnormalized weights. -/
theorem finite_conditionalEntropy_map_condition {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) (f : β → γ) :
    finiteEntropy p - finiteEntropy (finitePush p Prod.snd) ≤
      finiteEntropy (finitePush p (mapSecond f)) - finiteEntropy (finitePush (finitePush p Prod.snd) f) := by
  have h := finiteRelEntropy_push_le p (pairMarginalReference p) (mapSecond f) hp
    (pairMarginalReference_nonneg p hp) (pairMarginalReference_pos p hp)
  rw [finitePush_pairMarginalReference, finiteRelEntropy_pairMarginalReference p hp,
    finiteRelEntropy_pairMarginalReference _ (finitePush_nonneg p (mapSecond f) hp),
    finitePush_mapSecond_fst, finitePush_mapSecond_snd] at h
  linarith

end
end Erdos539Geometry
