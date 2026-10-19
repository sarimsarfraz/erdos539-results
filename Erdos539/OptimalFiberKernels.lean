/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiberKernelLift
import Erdos539.CouplingKernel

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- The identity transition, also defined on an empty finite type. -/
def identityKernel (α : Type*) [Fintype α] : FiniteMarkovKernel α α where
  weight a x := if x = a then 1 else 0
  nonneg a x := by split_ifs <;> norm_num
  sum_one a := by simp

theorem identityKernel_preserves {α : Type*} [Fintype α] (ν : α → ℝ) :
    (identityKernel α).Preserves ν := by
  funext x
  rw [finitePush_snd]
  simp [FiniteMarkovKernel.joint, identityKernel, mul_ite]

/-- A simultaneous choice of optimal stationary transitions in every
actual conditioning fiber. It defines one transition on the original
support and preserves the original law exactly. Zero-mass fibers use
identity transitions and contribute zero to the entropy average. -/
theorem exists_optimal_fiber_kernel {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (f : α → β) (channel : α → α → γ) :
    ∃ k : FiniteMarkovKernel α α, k.Preserves ν ∧
      (∀ a x, k.weight a x ≠ 0 → f x = f a) ∧
      (∑ a, ν a * finiteEntropy (finitePush (k.weight a) (channel a))) =
        ∑ b, finitePush ν f b * stationaryCapacity (conditionalWeight ν f b)
          (fun a x ↦ channel a.val x.val) := by
  have hex (b : β) : ∃ k : FiniteMarkovKernel {a // f a = b} {a // f a = b},
      k.Preserves (conditionalWeight ν f b) ∧
      finitePush ν f b * (∑ a, conditionalWeight ν f b a *
        finiteEntropy (finitePush (k.weight a) (fun x ↦ channel a.val x.val))) =
      finitePush ν f b * stationaryCapacity (conditionalWeight ν f b) (fun a x ↦ channel a.val x.val) := by
    by_cases hb : finitePush ν f b = 0
    · refine ⟨identityKernel _, identityKernel_preserves _, ?_⟩
      simp [hb]
    · let η := conditionalWeight ν f b
      have hη : ∀ a, 0 ≤ η a := conditionalWeight_nonneg ν hν f b
      have hsum : ∑ a, η a = 1 := conditionalWeight_sum ν f b hb
      let c : {a // f a = b} → {a // f a = b} → γ := fun a x ↦ channel a.val x.val
      obtain ⟨p, hp, he⟩ := stationaryCapacity_attained η hη hsum c
      let hr := stationaryCouplings_subset_rowCouplings η hp
      let k := couplingKernel η hη p hr
      refine ⟨k, couplingKernel_preserves η hη p hp, ?_⟩
      have h := couplingOutputEntropy_eq_kernel_average η hη p hr c
      change couplingOutputEntropy η c p = ∑ a, η a * finiteEntropy (finitePush (k.weight a) (c a)) at h
      change finitePush ν f b * (∑ a, η a * finiteEntropy (finitePush (k.weight a) (c a))) =
        finitePush ν f b * stationaryCapacity η c
      rw [← h, he]
  choose K hK hentropy using hex
  refine ⟨fiberKernel f K, fiberKernel_preserves ν hν f K hK, fiberKernel_support f K, ?_⟩
  rw [fiberKernel_output_average ν hν f K channel]
  exact Finset.sum_congr rfl (fun b _ ↦ hentropy b)

end
end Erdos539Geometry
