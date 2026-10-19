/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- The finite union-bound existence principle, with the actual failure
probabilities as finite sums of the normalized nonnegative sampling law. -/
theorem finite_avoidance {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) (bad : J → Ω → Prop)
    (hb : (∑ j, ∑ ω ∈ Finset.univ.filter (bad j), p ω) < 1) :
    ∃ ω, ∀ j, ¬bad j ω := by
  by_contra h
  push_neg at h
  have hpoint (ω : Ω) : p ω ≤ ∑ j, if bad j ω then p ω else 0 := by
    obtain ⟨j, hj⟩ := h ω
    calc
      p ω = if bad j ω then p ω else 0 := by rw [if_pos hj]
      _ ≤ _ := Finset.single_le_sum (f := fun i : J ↦ if bad i ω then p ω else (0 : ℝ))
        (fun i _ ↦ by dsimp only; split; exact hp ω; exact le_rfl) (Finset.mem_univ j)
  have hh := Finset.sum_le_sum (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) ↦ hpoint ω)
  rw [hs, Finset.sum_comm] at hh
  simp only [Finset.sum_filter] at hb
  linarith

end
end Erdos539Geometry
