/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SmallCoverCutAllowance

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local instance smallFourCoverRealDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- Any proper exposed fractional cover of weight at most two supported on
at most four masks gives one nontrivial physical cut. The two marginals
and all weighted products use the same arbitrary exact root optimizer. -/
theorem small_four_cover_compatible_cut (hcrit : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {m : ℕ} (hm : m ≤ 4) (A : Fin m → Finset ι) (c : Fin m → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hproper : ∀ k, ∃ x, x ∉ A k) (hexposed : ∀ k, IsExposedActiveMask T (A k))
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0) (hr : ∑ k, c k ≤ 2)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hopt : weightedEnergy T (extendWeight T f) = energyNorm T) :
    ∃ J : Finset ι, J.Nonempty ∧ (Finset.univ \ J).Nonempty ∧
      Real.log (actualMarginalEnergy T (extendWeight T f) J) ≤ Real.log (maxFan T) + smallCoverCutAllowance T b ∧
      Real.log (actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J)) ≤
        Real.log (maxFan T) + smallCoverCutAllowance T b ∧
      ∀ a r : ℝ, 0 ≤ a → 0 ≤ r →
        actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J) ^ a *
          actualMarginalEnergy T (extendWeight T f) J ^ r ≤
            Real.exp ((a + r) * smallCoverCutAllowance T b) * (maxFan T : ℝ) ^ (a + r) := by
  suffices hex : ∃ J : Finset ι, J.Nonempty ∧ (Finset.univ \ J).Nonempty ∧
      Real.log (actualMarginalEnergy T (extendWeight T f) J) ≤ Real.log (maxFan T) + smallCoverCutAllowance T b ∧
      Real.log (actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J)) ≤
        Real.log (maxFan T) + smallCoverCutAllowance T b by
    obtain ⟨J, hJ, hC, hl, hr⟩ := hex
    refine ⟨J, hJ, hC, hl, hr, ?_⟩
    intro a r ha hrr
    apply weighted_product_le_of_log_bounds _ _ _ ha hrr hr hl
    · exact lt_of_lt_of_le zero_lt_one (actualMarginalEnergy_unit_bounds T (Finset.univ \ J) f hf.2).1
    · exact lt_of_lt_of_le zero_lt_one (actualMarginalEnergy_unit_bounds T J f hf.2).1
    · exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hcrit.nonempty)
  by_cases hpair : ∃ i j, A i ∪ A j = Finset.univ
  · obtain ⟨i, j, hij⟩ := hpair
    have hJ : (A i).Nonempty := by
      obtain ⟨x, hx⟩ := hproper j
      have hu : x ∈ A i ∪ A j := hij ▸ Finset.mem_univ x
      exact ⟨x, (Finset.mem_union.mp hu).resolve_right hx⟩
    have hC : (Finset.univ \ A i).Nonempty := by
      obtain ⟨x, hx⟩ := hproper i
      exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩
    exact ⟨A i, hJ, hC, hcrit.exposed_two_mask_log_cut hb (hexposed i) (hexposed j) hij f hf.2⟩
  · have hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j := by
      intro i j _
      by_contra hn
      apply hpair
      refine ⟨i, j, Finset.eq_univ_of_forall ?_⟩
      intro x
      by_contra hx
      have hx' : x ∉ A i ∧ x ∉ A j := by simpa only [Finset.mem_union, not_or] using hx
      exact hn ⟨x, hx'⟩
    have hm4 := small_mask_cover_card hm A c hc hproper hcover hr hmiss
    subst m
    obtain ⟨J, hJ⟩ := hcrit.four_mask_weighted_cuts hb A c hc hexposed hcover hr hmiss hf hopt
    obtain ⟨_, hne, hcne, hl, hr, _⟩ := hJ 0
    have ha := add_le_add (le_rfl : Real.log (maxFan T) ≤ Real.log (maxFan T)) (hcrit.four_mask_allowance_le hf hopt)
    exact ⟨J 0, hne, hcne, hl.trans ha, hr.trans ha⟩

end IsProjectionCriticalCore
end
end Erdos539Geometry
