/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteConditioning
import Erdos539.FiniteCouplings

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem couplingOutputEntropy_map_injective {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (ν : α → ℝ) (channel : α → α → β) (f : β → γ) (hf : Function.Injective f)
    (p : α × α → ℝ) :
    couplingOutputEntropy ν (fun a x ↦ f (channel a x)) p = couplingOutputEntropy ν channel p := by
  have hmap : (fun z : α × α ↦ (z.1, f (channel z.1 z.2))) =
      mapSecond f ∘ (fun z ↦ (z.1, channel z.1 z.2)) := rfl
  unfold couplingOutputEntropy
  rw [hmap, ← finitePush_comp]
  congr 1
  apply finiteEntropy_push_eq_of_support_injective
  intro a b _ _ he
  apply Prod.ext
  · have hfirst := congrArg Prod.fst he
    exact hfirst
  · have hsecond := congrArg Prod.snd he
    exact hf hsecond

/-- Injectively relabeling outputs preserves the actual stationary
optimization, even when the ambient output alphabet has unused labels. -/
theorem stationaryCapacity_map_injective {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (ν : α → ℝ) (channel : α → α → β) (f : β → γ) (hf : Function.Injective f) :
    stationaryCapacity ν (fun a x ↦ f (channel a x)) = stationaryCapacity ν channel := by
  have he : couplingOutputEntropy ν (fun a x ↦ f (channel a x)) = couplingOutputEntropy ν channel :=
    funext (couplingOutputEntropy_map_injective ν channel f hf)
  unfold stationaryCapacity
  rw [he]

end
end Erdos539Geometry
