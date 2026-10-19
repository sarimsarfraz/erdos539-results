/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteCouplingEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Conditional entropy is bounded by the actual number of available
outputs in each row, including rows with zero probability. -/
theorem finite_conditionalEntropy_le_log_rows {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) (hfirst : finitePush p Prod.fst = ν)
    (A : α → Finset β) (hA : ∀ a, (A a).Nonempty)
    (hsupport : ∀ z, p z ≠ 0 → z.2 ∈ A z.1) :
    finiteEntropy p - finiteEntropy ν ≤ ∑ a, ν a * Real.log (A a).card := by
  let w : α × β → ℝ := fun z ↦ if z.2 ∈ A z.1 then ν z.1 / (A z.1).card else 0
  have hcard : ∀ a, (0 : ℝ) < (A a).card := fun a ↦ by exact_mod_cast (hA a).card_pos
  have hwrow : ∀ a, (∑ b, w (a, b)) = ν a := by
    intro a
    change (∑ b, if b ∈ A a then ν a / (A a).card else 0) = ν a
    rw [Fintype.sum_ite_mem]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp [(hcard a).ne']
  have hws : ∑ z, w z = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hwrow]
    exact hs
  have hps : ∑ z, p z = 1 := by rw [← finitePush_sum p Prod.fst, hfirst, hs]
  have hpos : ∀ z, p z ≠ 0 → 0 < ν z.1 := by
    intro z hz
    have hpoz := lt_of_le_of_ne (hp z) (Ne.symm hz)
    have hle := le_finitePush p Prod.fst hp z
    rw [hfirst] at hle
    exact hpoz.trans_le hle
  have hw : ∀ z, 0 ≤ w z := by
    intro z
    dsimp [w]
    split_ifs
    · exact div_nonneg (hν z.1) (hcard z.1).le
    · rfl
  have hwpos : ∀ z, p z ≠ 0 → 0 < w z := by
    intro z hz
    dsimp only [w]
    rw [if_pos (hsupport z hz)]
    exact div_pos (hpos z hz) (hcard z.1)
  have hlog : ∀ z, p z * Real.log (w z) =
      p z * (Real.log (ν z.1) - Real.log (A z.1).card) := by
    intro z
    by_cases hz : p z = 0
    · simp [hz]
    dsimp only [w]
    rw [if_pos (hsupport z hz), Real.log_div (hpos z hz).ne' (hcard z.1).ne']
  have hg := finiteEntropy_le_crossEntropy p w hp hps hw hws hwpos
  simp only [hlog] at hg
  have he := finitePush_expectation p Prod.fst (fun a ↦ Real.log (ν a) - Real.log (A a).card)
  rw [hfirst] at he
  rw [← he] at hg
  simp only [mul_sub, Finset.sum_sub_distrib] at hg
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib] at hg ⊢
  linarith

theorem couplingOutputEntropy_le_log_rows {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (A : α → Finset β) (hA : ∀ a, (A a).Nonempty)
    (hchannel : ∀ a x, channel a x ∈ A a) {p : α × α → ℝ} (hp : p ∈ stationaryCouplings ν) :
    couplingOutputEntropy ν channel p ≤ ∑ a, ν a * Real.log (A a).card := by
  apply finite_conditionalEntropy_le_log_rows ν hν hs _ (finitePush_nonneg _ _ hp.1) _ A hA
  · intro z hz
    by_contra hmem
    apply hz
    apply finitePush_eq_zero_of_fiber_zero
    intro y hy
    have hleft := congrArg Prod.fst hy
    have hright := congrArg Prod.snd hy
    have hm := hchannel y.1 y.2
    change y.1 = z.1 at hleft
    change channel y.1 y.2 = z.2 at hright
    rw [hright, hleft] at hm
    exact False.elim (hmem hm)
  · rw [finitePush_comp]
    exact hp.2.1

theorem stationaryCapacity_le_log_rows {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (A : α → Finset β) (hA : ∀ a, (A a).Nonempty)
    (hchannel : ∀ a x, channel a x ∈ A a) :
    stationaryCapacity ν channel ≤ ∑ a, ν a * Real.log (A a).card := by
  obtain ⟨p, hp, he⟩ := stationaryCapacity_attained ν hν hs channel
  rw [← he]
  exact couplingOutputEntropy_le_log_rows ν hν hs channel A hA hchannel hp

end
end Erdos539Geometry
