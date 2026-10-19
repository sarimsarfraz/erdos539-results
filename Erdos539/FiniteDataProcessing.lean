/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteRelativeEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Relative entropy decreases under a deterministic map. The proof is
the finite log-sum inequality in each actual fiber, including zero fibers. -/
theorem finiteRelEntropy_push_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (f : α → β) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hsupport : ∀ x, p x ≠ 0 → 0 < q x) :
    finiteRelEntropy (finitePush p f) (finitePush q f) ≤ finiteRelEntropy p q := by
  have hpoint : ∀ b, finitePush p f b * (Real.log (finitePush p f b) - Real.log (finitePush q f b)) ≤
      finitePush (fun x ↦ p x * (Real.log (p x) - Real.log (q x))) f b := by
    intro b
    have h := finite_log_sum (fun x ↦ if f x = b then p x else 0)
      (fun x ↦ if f x = b then q x else 0)
      (fun x ↦ by dsimp only; split_ifs; exact hp x; rfl)
      (fun x ↦ by dsimp only; split_ifs; exact hq x; rfl)
      (by
        intro x hx
        by_cases hfx : f x = b
        · simp only [if_pos hfx] at hx ⊢
          exact hsupport x hx
        · simp [hfx] at hx)
    change finitePush p f b * (Real.log (finitePush p f b) - Real.log (finitePush q f b)) ≤ _ at h
    convert h using 1
    unfold finiteRelEntropy finitePush
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : f x = b <;> simp [hx]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ hpoint b)
  rw [finitePush_sum] at hsum
  exact hsum

/-- Entropy is preserved by a deterministic map injective on the actual
nonzero support. The ambient domain may contain arbitrary zero atoms. -/
theorem finiteEntropy_push_eq_of_support_injective {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β)
    (hinj : ∀ a b, p a ≠ 0 → p b ≠ 0 → f a = f b → a = b) :
    finiteEntropy (finitePush p f) = finiteEntropy p := by
  have hval : ∀ a, p a ≠ 0 → finitePush p f (f a) = p a := by
    intro a ha
    unfold finitePush
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      by_cases hb : p b = 0
      · simp [hb]
      · have hne : f b ≠ f a := fun h ↦ hba (hinj b a hb ha h)
        simp [hne]
    · simp
  have he := finitePush_expectation p f (fun b ↦ -Real.log (finitePush p f b))
  calc
    finiteEntropy (finitePush p f) = ∑ a, p a * (-Real.log (finitePush p f (f a))) := by
      simpa only [finiteEntropy, Real.negMulLog, mul_neg, neg_mul] using he
    _ = finiteEntropy p := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : p a = 0
      · simp [ha]
      · rw [hval a ha]
        simp only [Real.negMulLog, mul_neg, neg_mul]

end
end Erdos539Geometry
