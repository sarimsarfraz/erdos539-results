/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteKernelEntropy
import Erdos539.FiniteEntropyKernel

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem FiniteMarkovKernel.output_entropy_average {α β : Type*} [Fintype α] [Fintype β]
    (k : FiniteMarkovKernel α β) (ρ : α → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (hs : ∑ a, ρ a = 1) :
    (∑ a, ρ a * finiteEntropy (k.weight a)) ≤
      finiteEntropy (finitePush (k.joint ρ) Prod.snd) := by
  have h := k.output_entropy_increment ρ hρ (fun _ ↦ ())
  have hc : finiteEntropy (finitePush ρ (fun _ ↦ ())) = 0 := by
    have he : finitePush ρ (fun _ ↦ ()) = fun _ : Unit ↦ (1 : ℝ) := by
      funext u
      cases u
      simpa only [finitePush, if_true] using hs
    rw [he]
    simp [finiteEntropy]
  have he := finiteEntropy_push_eq_of_same_fibers (k.joint ρ)
    (fun z : α × β ↦ ((), z.2)) Prod.snd (fun a b ↦ by simp)
  rw [hc, zero_add, he] at h
  exact h

/-- Entropy of a genuine finite mixture is at least the mean entropy of
its component observations; projected component supports may overlap. -/
theorem finiteEntropy_mixture_observation {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (ρ : α → ℝ) (ν : β → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (hsρ : ∑ a, ρ a = 1)
    (hν : ∀ b, 0 ≤ ν b) (hsν : ∑ b, ν b = 1) (f : α → β → γ) :
    (∑ a, ρ a * finiteEntropy (finitePush ν (f a))) ≤
      finiteEntropy (finitePush (fun z : α × β ↦ ρ z.1 * ν z.2) (fun z ↦ f z.1 z.2)) := by
  let k : FiniteMarkovKernel α β := ⟨fun _ ↦ ν, fun _ ↦ hν, fun _ ↦ hsν⟩
  have h := (k.mapOutput f).output_entropy_average ρ hρ hsρ
  rw [← k.joint_mapOutput ρ f, finitePush_comp] at h
  exact h

end
end Erdos539Geometry
