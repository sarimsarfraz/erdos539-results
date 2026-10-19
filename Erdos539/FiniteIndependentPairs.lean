/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteSameFiberCoupling

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

def independentPairWeight {α : Type*} (ν : α → ℝ) (z : α × α) : ℝ := ν z.1 * ν z.2

theorem independentPairWeight_first {α : Type*} [Fintype α]
    (ν : α → ℝ) (hs : ∑ x, ν x = 1) : finitePush (independentPairWeight ν) Prod.fst = ν := by
  funext x
  rw [finitePush_fst]
  simp only [independentPairWeight, ← Finset.mul_sum, hs, mul_one]

theorem independentPairWeight_second {α : Type*} [Fintype α]
    (ν : α → ℝ) (hs : ∑ x, ν x = 1) : finitePush (independentPairWeight ν) Prod.snd = ν := by
  funext x
  rw [finitePush_snd]
  simp only [independentPairWeight, ← Finset.sum_mul, hs, one_mul]

theorem independentPairWeight_entropy {α : Type*} [Fintype α]
    (ν : α → ℝ) (hs : ∑ x, ν x = 1) : finiteEntropy (independentPairWeight ν) = 2 * finiteEntropy ν := by
  have h := finiteEntropy_rows ν (fun _ ↦ ν) (fun _ ↦ hs)
  simp only [← Finset.sum_mul, hs, one_mul] at h
  change finiteEntropy (fun z : α × α ↦ ν z.1 * ν z.2) = _
  rw [h]
  ring

/-- A coupling of two independent-endpoint pairs has the same law at
all four endpoints. This does not assert additive support. -/
theorem independentPairCoupling_marginals {α : Type*} [Fintype α]
    (ν : α → ℝ) (hs : ∑ x, ν x = 1)
    (p : (α × α) × (α × α) → ℝ)
    (hfirst : finitePush p Prod.fst = independentPairWeight ν)
    (hsecond : finitePush p Prod.snd = independentPairWeight ν) :
    finitePush p (fun z ↦ z.1.1) = ν ∧ finitePush p (fun z ↦ z.1.2) = ν ∧
      finitePush p (fun z ↦ z.2.1) = ν ∧ finitePush p (fun z ↦ z.2.2) = ν := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change finitePush p (Prod.fst ∘ Prod.fst) = ν
    rw [← finitePush_comp, hfirst, independentPairWeight_first ν hs]
  · change finitePush p (Prod.snd ∘ Prod.fst) = ν
    rw [← finitePush_comp, hfirst, independentPairWeight_second ν hs]
  · change finitePush p (Prod.fst ∘ Prod.snd) = ν
    rw [← finitePush_comp, hsecond, independentPairWeight_first ν hs]
  · change finitePush p (Prod.snd ∘ Prod.snd) = ν
    rw [← finitePush_comp, hsecond, independentPairWeight_second ν hs]

end
end Erdos539Geometry
