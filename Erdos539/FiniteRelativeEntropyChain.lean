/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteConditionalLaws
import Erdos539.FiniteRelativeEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- The exact relative-entropy chain rule on literal finite fibers.
The reference is positive; the carried law can have zero atoms or fibers,
which contribute zero. Neither law needs to be normalized. -/
theorem finiteRelEntropy_fiber_chain {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x) (f : α → β) :
    finiteRelEntropy p q = finiteRelEntropy (finitePush p f) (finitePush q f) +
      ∑ b, finitePush p f b * finiteRelEntropy (conditionalWeight p f b) (conditionalWeight q f b) := by
  have hpoint (b : β) (x : {x // f x = b}) :
      p x.val * (Real.log (p x.val) - Real.log (q x.val)) =
        p x.val * (Real.log (finitePush p f b) - Real.log (finitePush q f b)) +
          finitePush p f b * (conditionalWeight p f b x *
            (Real.log (conditionalWeight p f b x) - Real.log (conditionalWeight q f b x))) := by
    by_cases hx : p x.val = 0
    · simp [hx, conditionalWeight]
    have hpx : 0 < p x.val := lt_of_le_of_ne (hp _) (Ne.symm hx)
    have hpm : 0 < finitePush p f b := by
      have h := hpx.trans_le (le_finitePush p f hp x.val)
      rwa [x.property] at h
    have hqm : 0 < finitePush q f b := by
      have h := (hq x.val).trans_le (le_finitePush q f (fun x ↦ (hq x).le) x.val)
      rwa [x.property] at h
    have hmass := conditionalWeight_mul_mass p hp f b x
    rw [← mul_assoc, hmass]
    rw [conditionalWeight, conditionalWeight,
      Real.log_div hx hpm.ne', Real.log_div (hq x.val).ne' hqm.ne']
    ring
  change (∑ x, p x * (Real.log (p x) - Real.log (q x))) = _
  rw [← Fintype.sum_fiberwise f (fun x ↦ p x * (Real.log (p x) - Real.log (q x)))]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← finitePush_eq_sum_fiber]
  rfl

end
end Erdos539Geometry
