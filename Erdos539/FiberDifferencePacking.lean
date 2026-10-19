/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsImageFibers

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

omit [DecidableEq H] in
theorem fiber_sub_label (S : Finset G) (φ : G →+ H) (y z : H) {x : G}
    (hx : x ∈ fiber S φ y - fiber S φ z) : φ x = y - z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
  rw [map_sub, (mem_fiber.mp ha).2, (mem_fiber.mp hb).2]

/-- All mixed differences against one fixed reference fiber have distinct
projection labels, so their cardinalities can be summed without overlap. -/
theorem sum_card_fiber_sub_le (S : Finset G) (φ : G →+ H) (z : H) :
    (∑ y : S.image φ, (fiber S φ y.val - fiber S φ z).card) ≤ (S - S).card := by
  let D : S.image φ → Finset G := fun y ↦ fiber S φ y.val - fiber S φ z
  have hdisj : (↑(Finset.univ : Finset (S.image φ)) : Set (S.image φ)).PairwiseDisjoint D := by
    intro y _ w _ hyw
    apply Finset.disjoint_left.mpr
    intro x hy hw
    have he : y.val - z = w.val - z := (fiber_sub_label S φ y.val z hy).symm.trans (fiber_sub_label S φ w.val z hw)
    exact hyw (Subtype.ext (sub_left_inj.mp he))
  have hsub : (Finset.univ.biUnion D) ⊆ S - S := by
    intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_sub.mp hy
    exact Finset.mem_sub.mpr ⟨a, (mem_fiber.mp ha).1, b, (mem_fiber.mp hb).1, he⟩
  change (∑ y, (D y).card) ≤ _
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card hsub

end
end Erdos539Geometry
