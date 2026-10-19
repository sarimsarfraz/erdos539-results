/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RowPointEnergyFormula
import Erdos539.UniformProductConditional

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def rowPointReference (S : Finset G) (x : rowPointSupport S) : ℝ :=
  if x.val.2 = 0 then 1 / (2 * S.card) else 1 / 2

theorem rowPointSupport_image (S : Finset G) (h0 : (0 : G) ∈ S) :
    (rowPointSupport S).image Prod.snd = ({0, 1} : Finset ℤ) := by
  rw [rowPointSupport, Finset.image_union, Finset.product_image_snd ⟨0, h0⟩]
  simp

theorem rowPointSupport_fiber_zero (S : Finset G) :
    fiber (rowPointSupport S) Prod.snd 0 = S ×ˢ ({0} : Finset ℤ) := by
  ext ⟨x, y⟩
  simp only [mem_fiber, rowPointSupport, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Prod.mk.injEq]
  norm_num
  aesop

theorem rowPointSupport_fiber_one (S : Finset G) :
    fiber (rowPointSupport S) Prod.snd 1 = {(0, 1)} := by
  ext ⟨x, y⟩
  simp only [mem_fiber, rowPointSupport, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Prod.mk.injEq]
  norm_num
  aesop

theorem rowPointReference_marginal (S : Finset G) (h0 : (0 : G) ∈ S)
    (y : (rowPointSupport S).image Prod.snd) :
    finitePush (rowPointReference S) (imageEndpoint (rowPointSupport S) Prod.snd) y = 1 / 2 := by
  have hy : y.val = 0 ∨ y.val = 1 := by
    simpa only [rowPointSupport_image S h0, Finset.mem_insert, Finset.mem_singleton] using y.property
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨0, h0⟩).ne'
  rw [finitePush_imageEndpoint_eq_fiber]
  change (∑ x : fiber (rowPointSupport S) Prod.snd y.val,
    if x.val.2 = 0 then 1 / (2 * (S.card : ℝ)) else 1 / 2) = _
  have he : (fun x : fiber (rowPointSupport S) Prod.snd y.val ↦
      if x.val.2 = 0 then 1 / (2 * (S.card : ℝ)) else 1 / 2) =
      fun _ ↦ if y.val = 0 then 1 / (2 * (S.card : ℝ)) else 1 / 2 := by
    funext x
    rw [(mem_fiber.mp x.property).2]
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  rcases hy with hy | hy
  · rw [hy, rowPointSupport_fiber_zero]
    simp [hn]
  · rw [hy, rowPointSupport_fiber_one]
    norm_num

theorem rowPointReference_nonneg (S : Finset G) (x : rowPointSupport S) :
    0 ≤ rowPointReference S x := by
  unfold rowPointReference
  split_ifs <;> positivity

theorem rowPointReference_sum (S : Finset G) (h0 : (0 : G) ∈ S) :
    ∑ x, rowPointReference S x = 1 := by
  rw [← finitePush_sum (rowPointReference S) (imageEndpoint (rowPointSupport S) Prod.snd)]
  simp only [rowPointReference_marginal S h0, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, rowPointSupport_image S h0]
  norm_num

theorem rowPointReference_conditional (S : Finset G) (h0 : (0 : G) ∈ S)
    (y : (rowPointSupport S).image Prod.snd) :
    imageFiberReference (rowPointSupport S) Prod.snd (rowPointReference S) y =
      uniformReference (fiber (rowPointSupport S) Prod.snd y.val) := by
  have hy : y.val = 0 ∨ y.val = 1 := by
    simpa only [rowPointSupport_image S h0, Finset.mem_insert, Finset.mem_singleton] using y.property
  funext x
  have hx : x.val.2 = y.val := (mem_fiber.mp x.property).2
  simp only [imageFiberReference, rowPointReference_marginal S h0,
    rowPointReference, uniformReference]
  change (if x.val.2 = 0 then 1 / (2 * (S.card : ℝ)) else 1 / 2) / (1 / 2) = _
  rw [hx]
  rcases hy with hy | hy
  · rw [hy, rowPointSupport_fiber_zero]
    simp
  · rw [hy, rowPointSupport_fiber_one]
    norm_num

end
end Erdos539Geometry
