/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteUniformImage

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- Two surjective observations with the same fibers have equally many values. -/
theorem finite_card_eq_of_same_fibers {α β γ : Type*} [Fintype β] [Fintype γ]
    (f : α → β) (g : α → γ) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a b, f a = f b ↔ g a = g b) : Fintype.card β = Fintype.card γ := by
  let u : γ → β := fun c ↦ f (hg c).choose
  have hu (a : α) : u (g a) = f a := by
    apply (h _ _).mpr
    exact (hg (g a)).choose_spec
  have hi : Function.Injective u := by
    intro c d he
    have hh := (h (hg c).choose (hg d).choose).mp he
    simpa only [(hg c).choose_spec, (hg d).choose_spec] using hh
  have hs : Function.Surjective u := by
    intro b
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨g a, hu a⟩
  exact (Fintype.card_congr (Equiv.ofBijective u ⟨hi, hs⟩)).symm

end
end Erdos539Geometry
