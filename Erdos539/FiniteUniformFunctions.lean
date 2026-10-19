/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductSupportLaws
import Erdos539.StationaryUniformDefect

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

def finiteUniformWeight (α : Type*) [Fintype α] : α → ℝ := fun _ ↦ 1 / Fintype.card α

theorem finiteUniformWeight_nonneg (α : Type*) [Fintype α] (a : α) :
    0 ≤ finiteUniformWeight α a := by unfold finiteUniformWeight; positivity

theorem finiteUniformWeight_sum (α : Type*) [Fintype α] [Nonempty α] :
    ∑ a, finiteUniformWeight α a = 1 := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  simp [finiteUniformWeight, h]

theorem finiteUniformWeight_entropy (α : Type*) [Fintype α] [Nonempty α] :
    finiteEntropy (finiteUniformWeight α) = Real.log (Fintype.card α : ℝ) := by
  have h := finiteEntropy_normalize (fun _ : α ↦ (1 : ℝ))
    (show 0 < ∑ _ : α, (1 : ℝ) by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]; exact_mod_cast Fintype.card_pos)
  change finiteEntropy (fun _ : α ↦ 1 / (Fintype.card α : ℝ)) = _
  simpa using h

theorem finiteUniformWeight_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    finitePush (finiteUniformWeight α) e = finiteUniformWeight β := by
  funext b
  rw [finitePush_equiv_apply]
  simp only [finiteUniformWeight, Fintype.card_congr e]

theorem finiteUniformWeight_product (α β : Type*) [Fintype α] [Fintype β] :
    finiteUniformWeight (α × β) = finiteProductWeight (finiteUniformWeight α) (finiteUniformWeight β) := by
  funext x
  simp [finiteUniformWeight, finiteProductWeight, Fintype.card_prod, mul_comm]

/-- The actual restriction of a uniformly sampled finite function is a
uniform function on the retained coordinates. -/
theorem finiteUniformWeight_restrict {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (I : Finset ι) :
    finitePush (finiteUniformWeight (ι → α)) (fun a (i : I) ↦ a i.val) =
      finiteUniformWeight (I → α) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i : ι ↦ i ∈ I) (fun _ ↦ α)
  have he := finiteUniformWeight_equiv e
  have h := congrArg (fun p ↦ finitePush p Prod.fst) he
  simp only [finitePush_comp, finiteUniformWeight_product] at h
  change finitePush (finiteUniformWeight (ι → α)) (fun a (i : I) ↦ a i.val) =
    finitePush (finiteProductWeight (finiteUniformWeight (I → α))
      (finiteUniformWeight (({i : ι // i ∉ I}) → α))) Prod.fst at h
  rw [h]
  funext a
  rw [finitePush_fst]
  simp only [finiteProductWeight, ← Finset.mul_sum, finiteUniformWeight_sum, mul_one]

theorem finiteUniformWeight_restrict_entropy {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (I : Finset ι) :
    finiteEntropy (finitePush (finiteUniformWeight (ι → α)) (fun a (i : I) ↦ a i.val)) =
      (I.card : ℝ) * Real.log (Fintype.card α : ℝ) := by
  rw [finiteUniformWeight_restrict, finiteUniformWeight_entropy]
  simp [Real.log_pow]

end
end Erdos539Geometry
