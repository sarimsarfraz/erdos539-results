/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RootColorMass
import Erdos539.ExposedOutput
import Erdos539.CoordinateShearer

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance exposedProjectionBoundsDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance exposedProjectionBoundsProjectionDecidableEq
    (S : Finset (ι → ℝ)) (I : Finset ι) : DecidableEq (projection S I) := Classical.decEq _

omit [Fintype ι] in
theorem coordinateProjectionEntropy_le_log_card {T : Finset (ι → ℝ)} (hT : T.Nonempty)
    (ν : T → ℝ) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (J : Finset ι) :
    coordinateProjectionEntropy T ν J ≤ Real.log (projection T J).card := by
  obtain ⟨x, hx⟩ := hT
  letI : Nonempty (projection T J) := ⟨projectEndpoint T J ⟨x, hx⟩⟩
  simpa only [Fintype.card_coe] using finiteEntropy_le_log_card
    (finitePush ν (projectEndpoint T J)) (finitePush_nonneg ν _ hν) (by rw [finitePush_sum, hs])

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- Every actual generic positive exposed mask has the claimed projection
bound, using full root criticality and an exact optimizer. -/
theorem exposed_projection_bound (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {J : Finset ι} (hJ : IsExposedActiveMask T J) :
    ((projection T J).card : ℝ) ≤
      (1 + 1 / b) * (posDiff T).card * (differences T).card / energyNorm T := by
  obtain ⟨w, z, hex⟩ := hJ
  obtain ⟨v, hv⟩ := hex.exists_color_killing_fiber
  exact h.color_killing_fiber_projection_bound hb J v z hv

theorem exposed_projection_log_bound (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {J : Finset ι} (hJ : IsExposedActiveMask T J) :
    Real.log (projection T J).card ≤ Real.log (1 + 1 / b) +
      Real.log (posDiff T).card + Real.log (differences T).card - Real.log (energyNorm T) := by
  have hs : 0 < 1 + 1 / b := by positivity
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hW : (0 : ℝ) < (differences T).card := by
    exact_mod_cast (h.nonempty.card_pos.trans_le (card_le_real_differences h.nonempty))
  obtain ⟨x, hx⟩ := h.nonempty
  have hp : (0 : ℝ) < (projection T J).card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨(projectEndpoint T J ⟨x, hx⟩).val,
      (projectEndpoint T J ⟨x, hx⟩).property⟩)
  have hl := Real.log_le_log hp (h.exposed_projection_bound hb hJ)
  rwa [Real.log_div (mul_pos (mul_pos hs hq) hW).ne' (energyNorm_pos h.nonempty).ne',
    Real.log_mul (mul_pos hs hq).ne' hW.ne', Real.log_mul hs.ne' hq.ne'] at hl

/-- A fractional cover of actual exposed masks bounds the entire root
optimizer entropy. Existence of a suitably small exposed cover is not
asserted. -/
theorem exposed_fractional_log_bound {κ : Type*} [Fintype κ]
    (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (A : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hexposed : ∀ k, IsExposedActiveMask T (A k))
    (hcover : ∀ i, 1 ≤ ∑ k, if i ∈ A k then c k else 0) :
    Real.log (energyNorm T) ≤ (∑ k, c k) *
      (Real.log (1 + 1 / b) + Real.log (posDiff T).card +
        Real.log (differences T).card - Real.log (energyNorm T)) := by
  obtain ⟨f, hfn, hfs, hE⟩ := energyNorm_attained h.nonempty
  have hf : f ∈ admissibleWeights T := ⟨hfn, hfs⟩
  have hl := (energyMaximizer_entropy_bounds h.nonempty hf hE).1
  have hsh := coordinate_fractional_entropy_cover T (fun x ↦ f x ^ 2)
    (fun x ↦ sq_nonneg (f x)) hfs A c hc hcover
  have hpoint (k : κ) := (coordinateProjectionEntropy_le_log_card h.nonempty
    (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)) hfs (A k)).trans
      (h.exposed_projection_log_bound hb (hexposed k))
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ ↦ mul_le_mul_of_nonneg_left (hpoint k) (hc k))
  rw [← Finset.sum_mul] at hsum
  exact hl.trans (hsh.trans hsum)

end IsProjectionCriticalCore
end
end Erdos539Geometry
