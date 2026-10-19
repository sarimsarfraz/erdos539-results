/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteDataProcessing

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Information depends only on the partition into fibers. A total
factor map into an option type handles unused observation labels. -/
theorem finiteEntropy_push_le_of_fiber_refinement {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (f : α → β) (g : α → γ)
    (hfg : ∀ a b, f a = f b → g a = g b) :
    finiteEntropy (finitePush p g) ≤ finiteEntropy (finitePush p f) := by
  let h : β → Option γ := fun b ↦
    if hb : ∃ a, f a = b then some (g (Classical.choose hb)) else none
  have hc : h ∘ f = some ∘ g := by
    funext a
    have ha : ∃ x, f x = f a := ⟨a, rfl⟩
    simp only [Function.comp_apply, h, dif_pos ha]
    exact congrArg some (hfg _ a (Classical.choose_spec ha))
  have he := finiteEntropy_push_eq_of_support_injective (finitePush p g) some
    (fun a b _ _ hab ↦ Option.some.inj hab)
  have hl := finiteEntropy_push_le (finitePush p f) h (finitePush_nonneg p f hp)
  rw [finitePush_comp, hc, ← finitePush_comp, he] at hl
  exact hl

theorem finiteEntropy_push_eq_of_fibers {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (f : α → β) (g : α → γ)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    finiteEntropy (finitePush p f) = finiteEntropy (finitePush p g) := by
  exact le_antisymm
    (finiteEntropy_push_le_of_fiber_refinement p hp g f (fun a b h ↦ (hfg a b).mpr h))
    (finiteEntropy_push_le_of_fiber_refinement p hp f g (fun a b h ↦ (hfg a b).mp h))

end
end Erdos539Geometry
