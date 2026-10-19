/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteEntropyMixtures

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem finitePush_eq_sum_fiber {α β : Type*} [Fintype α]
    (ν : α → ℝ) (f : α → β) (b : β) :
    finitePush ν f b = ∑ x : {x // f x = b}, ν x.val := by
  unfold finitePush
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Literal conditional weights in an actual fiber. A zero-mass fiber
has the identically zero conditional weight. -/
def conditionalWeight {α β : Type*} [Fintype α]
    (ν : α → ℝ) (f : α → β) (b : β) (x : {x // f x = b}) : ℝ :=
  ν x.val / finitePush ν f b

theorem conditionalWeight_nonneg {α β : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (f : α → β) (b : β) (x : {x // f x = b}) :
    0 ≤ conditionalWeight ν f b x := div_nonneg (hν x.val) (finitePush_nonneg ν f hν b)

theorem conditionalWeight_sum {α β : Type*} [Fintype α]
    (ν : α → ℝ) (f : α → β) (b : β) (hb : finitePush ν f b ≠ 0) :
    ∑ x, conditionalWeight ν f b x = 1 := by
  simp only [conditionalWeight, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← finitePush_eq_sum_fiber, mul_inv_cancel₀ hb]

theorem conditionalWeight_mul_mass {α β : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (f : α → β) (b : β) (x : {x // f x = b}) :
    finitePush ν f b * conditionalWeight ν f b x = ν x.val := by
  by_cases hb : finitePush ν f b = 0
  · have hle := le_finitePush ν f hν x.val
    rw [x.property, hb] at hle
    have hx := le_antisymm hle (hν x.val)
    simp [hb, hx]
  · dsimp [conditionalWeight]
    field_simp

/-- The actual finite conditional entropy chain rule, with zero-mass
fibers retained and contributing zero. -/
theorem finiteEntropy_fiber_chain {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (f : α → β) :
    finiteEntropy ν = finiteEntropy (finitePush ν f) +
      ∑ b, finitePush ν f b * finiteEntropy (conditionalWeight ν f b) := by
  have hrow (b : β) : (∑ x : {x // f x = b}, Real.negMulLog (ν x.val)) =
      Real.negMulLog (finitePush ν f b) + finitePush ν f b * finiteEntropy (conditionalWeight ν f b) := by
    have hpoint (x : {x // f x = b}) : Real.negMulLog (ν x.val) =
        conditionalWeight ν f b x * Real.negMulLog (finitePush ν f b) +
          finitePush ν f b * Real.negMulLog (conditionalWeight ν f b x) := by
      rw [← conditionalWeight_mul_mass ν hν f b x, Real.negMulLog_mul]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    by_cases hb : finitePush ν f b = 0
    · simp [hb]
    · rw [conditionalWeight_sum ν f b hb, one_mul]
      rfl
  unfold finiteEntropy
  rw [← Fintype.sum_fiberwise f (fun a ↦ Real.negMulLog (ν a))]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  rfl

/-- Pushforward through an injection retains each original atom. -/
theorem finitePush_apply_injective {α β : Type*} [Fintype α]
    (p : α → ℝ) (f : α → β) (hf : Function.Injective f) (a : α) :
    finitePush p f (f a) = p a := by
  unfold finitePush
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : f b ≠ f a := fun h ↦ hba (hf h)
    simp [hne]
  · simp

/-- Reconstruction of the original law from its actual conditional
fiber laws and their masses, including zero-mass fibers. -/
theorem conditionalWeight_disintegration {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (f : α → β) (a : α) :
    (∑ b, finitePush ν f b * finitePush (conditionalWeight ν f b) Subtype.val a) = ν a := by
  rw [Finset.sum_eq_single (f a)]
  · have he := finitePush_apply_injective (conditionalWeight ν f (f a))
      Subtype.val Subtype.val_injective (⟨a, rfl⟩ : {x // f x = f a})
    rw [he]
    exact conditionalWeight_mul_mass ν hν f (f a) ⟨a, rfl⟩
  · intro b _ hb
    have he : finitePush (conditionalWeight ν f b) Subtype.val a = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hxa : x.val ≠ a := by
        intro hx
        have h := x.property
        rw [hx] at h
        exact hb h.symm
      simp [hxa]
    rw [he, mul_zero]
  · simp

end
end Erdos539Geometry
