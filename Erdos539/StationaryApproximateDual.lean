/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteEntropyConcavity
import Erdos539.FiniteConcaveDuality

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- An actual potential for every positive dual tolerance. The comparison
holds on all row couplings, not only stationary ones. -/
theorem stationaryCapacity_approximate_potential {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : α → ℝ, ∀ p ∈ rowCouplings ν,
      couplingOutputEntropy ν channel p + (∑ a, ν a * t a) -
        (∑ z, p z * t z.2) < stationaryCapacity ν channel + ε := by
  obtain ⟨p₀, hp₀, he⟩ := stationaryCapacity_attained ν hν hs channel
  have hmax : ∀ p ∈ rowCouplings ν, finitePushLinear Prod.snd p = ν →
      couplingOutputEntropy ν channel p ≤ stationaryCapacity ν channel := by
    intro p hp hsecond
    have hstat : p ∈ stationaryCouplings ν := ⟨hp.1, hp.2, hsecond⟩
    obtain ⟨q, hq, hqmax⟩ := exists_stationaryCouplingMax ν hν hs channel
    have hg : IsGreatest (couplingOutputEntropy ν channel '' stationaryCouplings ν)
        (couplingOutputEntropy ν channel q) := ⟨⟨q, hq, rfl⟩, by
          rintro _ ⟨r, hr, rfl⟩
          exact hqmax r hr⟩
    rw [stationaryCapacity, hg.csSup_eq]
    exact hqmax p hstat
  obtain ⟨l, hl⟩ := finite_concave_approximate_dual (rowCouplings ν)
    (rowCouplings_isCompact ν hν hs) (finitePushLinear Prod.snd)
    (couplingOutputEntropy ν channel) (continuous_couplingOutputEntropy ν channel)
    (couplingOutputEntropy_concaveOn ν channel) ν (stationaryCapacity ν channel)
    p₀ (stationaryCouplings_subset_rowCouplings ν hp₀) hp₀.2.2 he hmax hε
  let t : α → ℝ := fun a ↦ l (Pi.single a 1)
  have hexp (v : α → ℝ) : l v = ∑ a, v a * t a := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, t]
  refine ⟨t, ?_⟩
  intro p hp
  have h := hl p hp
  rw [hexp, hexp] at h
  change couplingOutputEntropy ν channel p + (∑ a, ν a * t a) -
    (∑ a, finitePush p Prod.snd a * t a) < _ at h
  rw [finitePush_expectation] at h
  exact h

end
end Erdos539Geometry
