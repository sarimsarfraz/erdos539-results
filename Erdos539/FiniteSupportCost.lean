/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteRelativeEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- A probability supported on an event of reference mass at most r has
relative entropy at least -log r. Zero reference atoms are allowed. -/
theorem finiteRelEntropy_ge_support_cost {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hs : ∑ x, p x = 1) (E : α → Prop)
    (hE : ∀ x, p x ≠ 0 → E x) (hsupport : ∀ x, p x ≠ 0 → 0 < q x)
    {r : ℝ} (hr : (∑ x, if E x then q x else 0) ≤ r) :
    -Real.log r ≤ finiteRelEntropy p q := by
  let w : α → ℝ := fun x ↦ if E x then q x else 0
  have hw : ∀ x, 0 ≤ w x := by intro x; dsimp [w]; split; exact hq x; exact le_rfl
  have hwp : ∀ x, p x ≠ 0 → 0 < w x := by
    intro x hx
    simpa only [w, if_pos (hE x hx)] using hsupport x hx
  have hW : 0 < ∑ x, w x := by
    have hex : ∃ x, 0 < p x := by
      by_contra hn
      push_neg at hn
      have hz : ∀ x, p x = 0 := fun x ↦ le_antisymm (hn x) (hp x)
      simp only [hz, Finset.sum_const_zero] at hs
      norm_num at hs
    obtain ⟨x, hx⟩ := hex
    exact (hwp x hx.ne').trans_le (Finset.single_le_sum (fun y _ ↦ hw y) (Finset.mem_univ x))
  have he : finiteRelEntropy p w = finiteRelEntropy p q := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p x = 0
    · simp only [hx, zero_mul]
    · simp only [w, if_pos (hE x hx)]
  have h := finite_log_sum p w hp hw hwp
  rw [hs, Real.log_one, zero_sub, one_mul, he] at h
  exact (neg_le_neg (Real.log_le_log hW hr)).trans h

end
end Erdos539Geometry
