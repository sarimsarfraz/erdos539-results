/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelDuality

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Weak duality for every row coupling. The expectation uses its actual
target marginal; replacing it by the prescribed law requires stationarity. -/
theorem rowCoupling_le_channelDualValue {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (t : α → ℝ) {p : α × α → ℝ} (hp : p ∈ rowCouplings ν) :
    couplingOutputEntropy ν channel p + (∑ a, ν a * t a) -
      (∑ z, p z * t z.2) ≤ channelDualValue ν channel t := by
  let e : α × α → α × β := fun z ↦ (z.1, channel z.1 z.2)
  let q := finitePush p e
  let w : α × β → ℝ := fun z ↦ ν z.1 * channelSoftmax channel t z.1 z.2
  have hq : ∀ z, 0 ≤ q z := finitePush_nonneg p e hp.1
  have hfirst : finitePush q Prod.fst = ν := by rw [finitePush_comp]; exact hp.2
  have hqs : ∑ z, q z = 1 := by rw [← finitePush_sum q Prod.fst, hfirst, hs]
  have hw : ∀ z, 0 ≤ w z := fun z ↦ mul_nonneg (hν z.1) (channelSoftmax_nonneg channel t z.1 z.2)
  have hws : ∑ z, w z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [w, ← Finset.mul_sum, channelSoftmax_sum, mul_one]
    exact hs
  have hνpos (z : α × β) (hz : q z ≠ 0) : 0 < ν z.1 := by
    have hle := le_finitePush q Prod.fst hq z
    rw [hfirst] at hle
    exact (lt_of_le_of_ne (hq z) (Ne.symm hz)).trans_le hle
  have hout (z : α × β) (hz : q z ≠ 0) : z.2 ∈ channelOutputs channel z.1 := by
    by_contra hn
    apply hz
    apply finitePush_eq_zero_of_fiber_zero
    intro y hy
    have hy1 : y.1 = z.1 := congrArg Prod.fst hy
    have hy2 : channel y.1 y.2 = z.2 := congrArg Prod.snd hy
    have hm := mem_channelOutputs channel y.1 y.2
    rw [hy2, hy1] at hm
    exact False.elim (hn hm)
  have hwpos (z : α × β) (hz : q z ≠ 0) : 0 < w z := by
    dsimp [w, channelSoftmax]
    rw [channelReference, if_pos (hout z hz)]
    exact mul_pos (hνpos z hz) (div_pos (Real.exp_pos _) (channelPartition_pos channel t z.1))
  have hlog (z : α × β) : q z * Real.log (w z) = q z *
      (Real.log (ν z.1) - t (minPotentialRepresentative channel t z.1 z.2) -
        Real.log (channelPartition channel t z.1)) := by
    by_cases hz : q z = 0
    · simp [hz]
    · dsimp only [w, channelSoftmax]
      rw [channelReference, if_pos (hout z hz),
        Real.log_mul (hνpos z hz).ne' (div_ne_zero (Real.exp_ne_zero _) (channelPartition_pos channel t z.1).ne'),
        Real.log_div (Real.exp_ne_zero _) (channelPartition_pos channel t z.1).ne', Real.log_exp]
      ring
  have hg := finiteEntropy_le_crossEntropy q w hq hqs hw hws hwpos
  simp only [hlog, mul_sub, Finset.sum_sub_distrib] at hg
  have hlogν := finitePush_expectation q Prod.fst (fun a ↦ Real.log (ν a))
  have hlogW := finitePush_expectation q Prod.fst (fun a ↦ Real.log (channelPartition channel t a))
  rw [hfirst] at hlogν hlogW
  rw [← hlogν, ← hlogW] at hg
  have hcost : (∑ z, q z * t (minPotentialRepresentative channel t z.1 z.2)) ≤
      ∑ z, p z * t z.2 := by
    change (∑ z, finitePush p e z * (fun z : α × β ↦ t (minPotentialRepresentative channel t z.1 z.2)) z) ≤ _
    rw [finitePush_expectation]
    apply Finset.sum_le_sum
    intro z _
    apply mul_le_mul_of_nonneg_left _ (hp.1 z)
    exact (minPotentialRepresentative_spec channel t z.1 (mem_channelOutputs channel z.1 z.2)).2 z.2 rfl
  change finiteEntropy q - finiteEntropy ν + _ - _ ≤ _
  simp only [channelDualValue, mul_add, Finset.sum_add_distrib]
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib] at hg ⊢
  linarith

theorem stationaryCapacity_le_channelDualValue {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (t : α → ℝ) :
    stationaryCapacity ν channel ≤ channelDualValue ν channel t := by
  obtain ⟨p, hp, he⟩ := stationaryCapacity_attained ν hν hs channel
  have h := rowCoupling_le_channelDualValue ν hν hs channel t
    (stationaryCouplings_subset_rowCouplings ν hp)
  have hc := finitePush_expectation p Prod.snd t
  rw [hp.2.2] at hc
  rw [← hc, add_sub_cancel_right, he] at h
  exact h

/-- Exact finite entropy duality, with an infimum rather than an assumed
minimum. All formulas refer to the original law, including its zero atoms. -/
theorem stationaryCapacity_eq_inf_channelDualValue {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) :
    stationaryCapacity ν channel = sInf (Set.range (channelDualValue ν channel)) := by
  have hne : (Set.range (channelDualValue ν channel)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hb : BddBelow (Set.range (channelDualValue ν channel)) := by
    refine ⟨stationaryCapacity ν channel, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact stationaryCapacity_le_channelDualValue ν hν hs channel t
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨t, rfl⟩
    exact stationaryCapacity_le_channelDualValue ν hν hs channel t
  · by_contra hn
    have hgap : 0 < sInf (Set.range (channelDualValue ν channel)) - stationaryCapacity ν channel :=
      sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨t, ht⟩ := channelDualValue_approximate ν hν hs channel (half_pos hgap)
    have hle := csInf_le hb (Set.mem_range_self t)
    linarith

end
end Erdos539Geometry
