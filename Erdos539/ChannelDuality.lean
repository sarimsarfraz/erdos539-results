/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelPotentials
import Erdos539.StationaryApproximateDual

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- A literal row coupling attaining the unconstrained row optimization.
All output mass is placed at the selected minimum-potential representative. -/
theorem exists_rowCoupling_dual_value {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (channel : α → α → β) (t : α → ℝ) :
    ∃ p ∈ rowCouplings ν, couplingOutputEntropy ν channel p + (∑ a, ν a * t a) -
      (∑ z, p z * t z.2) = channelDualValue ν channel t := by
  let k := channelSoftmax channel t
  let r : α × β → ℝ := fun z ↦ ν z.1 * k z.1 z.2
  let g : α × β → α × α := fun z ↦ (z.1, minPotentialRepresentative channel t z.1 z.2)
  let e : α × α → α × β := fun z ↦ (z.1, channel z.1 z.2)
  let p := finitePush r g
  have hr : ∀ z, 0 ≤ r z := fun z ↦ mul_nonneg (hν z.1) (channelSoftmax_nonneg channel t z.1 z.2)
  have hfirst : finitePush r Prod.fst = ν := by
    funext a
    rw [finitePush_fst]
    change (∑ b, ν a * k a b) = ν a
    rw [← Finset.mul_sum, channelSoftmax_sum, mul_one]
  have hp : p ∈ rowCouplings ν := by
    refine ⟨finitePush_nonneg r g hr, ?_⟩
    rw [finitePush_comp]
    exact hfirst
  have hout : finitePush p e = r := by
    rw [finitePush_comp]
    have hm : finitePush r (e ∘ g) = finitePush r id := by
      apply finitePush_congr_on_support
      intro z hz
      have hk : k z.1 z.2 ≠ 0 := by intro h; apply hz; simp [r, h]
      have hrep := (minPotentialRepresentative_spec channel t z.1
        (channelSoftmax_support channel t z.1 hk)).1
      apply Prod.ext
      · rfl
      · exact hrep
    rw [hm, finitePush_id]
  have hent : couplingOutputEntropy ν channel p = ∑ a, ν a * finiteEntropy (k a) := by
    change finiteEntropy (finitePush p e) - finiteEntropy ν = _
    rw [hout, finiteEntropy_rows ν k (channelSoftmax_sum channel t)]
    ring
  have hcost : (∑ z, p z * t z.2) =
      ∑ a, ν a * ∑ b, k a b * t (minPotentialRepresentative channel t a b) := by
    change (∑ z, finitePush r g z * (fun z : α × α ↦ t z.2) z) = _
    rw [finitePush_expectation, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [r, g]
    ring
  refine ⟨p, hp, ?_⟩
  rw [hent, hcost]
  simp only [channelDualValue, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have he := channelSoftmax_entropy channel t a
  change finiteEntropy (k a) - (∑ z, k a z * t (minPotentialRepresentative channel t a z)) = _ at he
  rw [← he]
  ring

/-- Strong finite entropy duality in the form needed by the scalar proof:
the explicit minimum-representative expression approaches the stationary
capacity from above. No dual minimizer is assumed. -/
theorem channelDualValue_approximate {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : α → ℝ, channelDualValue ν channel t < stationaryCapacity ν channel + ε := by
  obtain ⟨t, ht⟩ := stationaryCapacity_approximate_potential ν hν hs channel hε
  obtain ⟨p, hp, he⟩ := exists_rowCoupling_dual_value ν hν channel t
  exact ⟨t, he ▸ ht p hp⟩

end
end Erdos539Geometry
