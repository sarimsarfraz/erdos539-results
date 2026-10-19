/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteCouplings

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem stationaryCoupling_entropy_le {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    {p : α × α → ℝ} (hp : p ∈ stationaryCouplings ν) :
    finiteEntropy p ≤ 2 * finiteEntropy ν := by
  let w : α × α → ℝ := fun z ↦ ν z.1 * ν z.2
  have hps : ∑ z, p z = 1 := by
    rw [← finitePush_sum p Prod.fst, hp.2.1, hs]
  have hws : ∑ z, w z = 1 := by
    simp only [w, Fintype.sum_prod_type, ← Finset.mul_sum, hs, mul_one]
  have hpos : ∀ z, p z ≠ 0 → 0 < ν z.1 ∧ 0 < ν z.2 := by
    intro z hz
    have hpoz : 0 < p z := lt_of_le_of_ne (hp.1 z) (Ne.symm hz)
    have ha := le_finitePush p Prod.fst hp.1 z
    have hb := le_finitePush p Prod.snd hp.1 z
    rw [hp.2.1] at ha
    rw [hp.2.2] at hb
    exact ⟨hpoz.trans_le ha, hpoz.trans_le hb⟩
  have hlog : ∀ z, p z * Real.log (w z) = p z * (Real.log (ν z.1) + Real.log (ν z.2)) := by
    intro z
    by_cases hz : p z = 0
    · simp [hz]
    obtain ⟨ha, hb⟩ := hpos z hz
    exact congrArg (p z * ·) (Real.log_mul ha.ne' hb.ne')
  have h₁ := finitePush_expectation p Prod.fst (fun a ↦ Real.log (ν a))
  have h₂ := finitePush_expectation p Prod.snd (fun a ↦ Real.log (ν a))
  rw [hp.2.1] at h₁
  rw [hp.2.2] at h₂
  have hg := finiteEntropy_le_crossEntropy p w hp.1 hps
    (fun z ↦ mul_nonneg (hν z.1) (hν z.2)) hws
    (fun z hz ↦ mul_pos (hpos z hz).1 (hpos z hz).2)
  simp only [hlog, mul_add, Finset.sum_add_distrib] at hg
  rw [← h₁, ← h₂] at hg
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib] at hg ⊢
  linarith

theorem couplingOutputEntropy_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (channel : α → α → β) {p : α × α → ℝ}
    (hp : p ∈ stationaryCouplings ν) : 0 ≤ couplingOutputEntropy ν channel p := by
  have h := finiteEntropy_push_le (finitePush p (fun z ↦ (z.1, channel z.1 z.2))) Prod.fst
    (finitePush_nonneg _ _ hp.1)
  rw [finitePush_comp] at h
  change finiteEntropy (finitePush p Prod.fst) ≤ _ at h
  rw [hp.2.1] at h
  exact sub_nonneg.mpr h

theorem couplingOutputEntropy_le {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (channel : α → α → β)
    {p : α × α → ℝ} (hp : p ∈ stationaryCouplings ν) :
    couplingOutputEntropy ν channel p ≤ finiteEntropy ν := by
  have hmap := finiteEntropy_push_le p (fun z ↦ (z.1, channel z.1 z.2)) hp.1
  have hjoint := stationaryCoupling_entropy_le ν hν hs hp
  unfold couplingOutputEntropy
  linarith

theorem stationaryCapacity_bounds {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (channel : α → α → β) :
    0 ≤ stationaryCapacity ν channel ∧ stationaryCapacity ν channel ≤ finiteEntropy ν := by
  obtain ⟨p, hp, he⟩ := stationaryCapacity_attained ν hν hs channel
  rw [← he]
  exact ⟨couplingOutputEntropy_nonneg ν channel hp, couplingOutputEntropy_le ν hν hs channel hp⟩

end
end Erdos539Geometry
