/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteFiberCard

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem card_image_le_of_fibers {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (S : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ S, ∀ b ∈ S, g a = g b → f a = f b) :
    (S.image f).card ≤ (S.image g).card := by
  let a (y : S.image f) : α := (Finset.mem_image.mp y.property).choose
  have ha (y : S.image f) : a y ∈ S ∧ f (a y) = y.val :=
    (Finset.mem_image.mp y.property).choose_spec
  let u : S.image f → S.image g := fun y ↦ ⟨g (a y), Finset.mem_image_of_mem _ (ha y).1⟩
  have hi : Function.Injective u := by
    intro y z he
    have hg : g (a y) = g (a z) := congrArg Subtype.val he
    apply Subtype.ext
    rw [← (ha y).2, ← (ha z).2]
    exact h (a y) (ha y).1 (a z) (ha z).1 hg
  simpa using Fintype.card_le_of_injective u hi

end
end Erdos539Geometry
