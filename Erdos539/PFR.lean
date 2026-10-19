/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0

Explicit reuse of the proved PFR theorem, without a new axiom or hypothesis.
The source theorem and its full dependency closure are vendored under PFR/.
-/
import PFR.WeakPFR

namespace Erdos539
open scoped Pointwise

/-- Weak PFR in its difference-doubling form, with the proved constants. -/
theorem weakPFR_integer
    {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    {A : Set G} [Finite A] (hA : A.Nonempty) {K : ℝ}
    (hd : (Nat.card (A - A) : ℝ) ≤ K * Nat.card A) :
    ∃ A' : Set G, A' ⊆ A ∧
      (Nat.card A' : ℝ) ≥ K ^ (-17 : ℝ) * Nat.card A ∧
      AffineSpace.finrank ℤ A' ≤ (40 / Real.log 2) * Real.log K :=
  weak_PFR_int hA hd

end Erdos539

#print axioms Erdos539.weakPFR_integer
