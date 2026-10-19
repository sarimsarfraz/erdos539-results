/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteIndependentPairs

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

def finiteProductWeight {α β : Type*} (p : α → ℝ) (q : β → ℝ) (z : α × β) : ℝ := p z.1 * q z.2

theorem finiteProductWeight_nonneg {α β : Type*} (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (z : α × β) : 0 ≤ finiteProductWeight p q z :=
  mul_nonneg (hp z.1) (hq z.2)

theorem finiteProductWeight_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) : (∑ z, finiteProductWeight p q z) = (∑ x, p x) * ∑ y, q y := by
  simp only [finiteProductWeight, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

theorem finiteProductWeight_entropy {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (hps : ∑ x, p x = 1) (hqs : ∑ y, q y = 1) :
    finiteEntropy (finiteProductWeight p q) = finiteEntropy p + finiteEntropy q := by
  have h := finiteEntropy_rows p (fun _ ↦ q) (fun _ ↦ hqs)
  simpa only [← Finset.sum_mul, hps, one_mul, finiteProductWeight] using h

/-- Independent factors remain independent under separate actual maps. -/
theorem finitePush_productMap {α β γ δ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (e : α → γ) (f : β → δ) :
    finitePush (finiteProductWeight p q) (Prod.map e f) = finiteProductWeight (finitePush p e) (finitePush q f) := by
  funext z
  simp only [finitePush, finiteProductWeight, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : e a = z.1 <;> by_cases hb : f b = z.2 <;> simp [ha, hb, Prod.ext_iff]

theorem finitePush_equiv_apply {α β : Type*} [Fintype α]
    (p : α → ℝ) (e : α ≃ β) (b : β) : finitePush p e b = p (e.symm b) := by
  simpa only [e.apply_symm_apply] using finitePush_apply_injective p e e.injective (e.symm b)

end
end Erdos539Geometry
