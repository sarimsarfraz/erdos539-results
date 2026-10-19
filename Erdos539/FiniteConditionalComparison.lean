/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteConditioning

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Comparison of an original conditional entropy with a coarser one.
The hypotheses explicitly identify the deterministic factor maps and
which pair of observations recovers the original state. -/
theorem finite_conditional_entropy_comparison {α β γ δ ε : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a)
    (X : α → β) (F : α → γ) (G : α → δ) (L : α → ε)
    (h : γ → δ) (g : ε → β × δ)
    (hG : h ∘ F = G) (hL : g ∘ L = fun a ↦ (X a, G a))
    (hinj : Function.Injective (fun a ↦ (X a, F a))) :
    finiteEntropy ν - finiteEntropy (finitePush ν F) ≤
      finiteEntropy (finitePush ν L) - finiteEntropy (finitePush ν G) := by
  let p := finitePush ν (fun a ↦ (X a, F a))
  have hp : ∀ z, 0 ≤ p z := finitePush_nonneg ν _ hν
  have hpH : finiteEntropy p = finiteEntropy ν :=
    finiteEntropy_push_eq_of_support_injective ν _ (fun a b _ _ he ↦ hinj he)
  have hpF : finitePush p Prod.snd = finitePush ν F := by
    rw [finitePush_comp]
    rfl
  have hpG : finitePush (finitePush ν F) h = finitePush ν G := by rw [finitePush_comp, hG]
  have hpL : finitePush p (mapSecond h) = finitePush (finitePush ν L) g := by
    rw [finitePush_comp, finitePush_comp, hL]
    congr 1
    funext a
    apply Prod.ext
    · rfl
    · exact congrFun hG a
  have hle := finite_conditionalEntropy_map_condition p hp h
  rw [hpH, hpF, hpG, hpL] at hle
  have hpush := finiteEntropy_push_le (finitePush ν L) g (finitePush_nonneg ν L hν)
  linarith

end
end Erdos539Geometry
