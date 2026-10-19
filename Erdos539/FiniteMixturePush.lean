/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProductLaws

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem finitePush_mixture_component {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (ρ : α → ℝ) (p : β → ℝ) (f : β → γ) (e : α → γ → δ) :
    finitePush (finiteProductWeight ρ p) (fun z ↦ e z.1 (f z.2)) =
      finitePush (finiteProductWeight ρ (finitePush p f)) (fun z ↦ e z.1 z.2) := by
  have h := finitePush_productMap ρ p (id : α → α) f
  rw [finitePush_id] at h
  rw [← h, finitePush_comp]
  rfl

end
end Erdos539Geometry
