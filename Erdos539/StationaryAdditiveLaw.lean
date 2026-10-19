/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.QuadrupleLaw
import Erdos539.FiniteGibbs

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- An actual nonnegative additive-quadruple weight with four identical
endpoint marginals. Normalization is supplied by the endpoint law. -/
structure StationaryAdditiveLaw (S : Finset G) (ν : S → ℝ) where
  mass : S → S → S → S → ℝ
  nonneg : ∀ a b c d, 0 ≤ mass a b c d
  supported : ∀ a b c d, a.val + b.val ≠ c.val + d.val → mass a b c d = 0
  first : ∀ a, (∑ b, ∑ c, ∑ d, mass a b c d) = ν a
  second : ∀ b, (∑ a, ∑ c, ∑ d, mass a b c d) = ν b
  third : ∀ c, (∑ a, ∑ b, ∑ d, mass a b c d) = ν c
  fourth : ∀ d, (∑ a, ∑ b, ∑ c, mass a b c d) = ν d

omit [AddCommGroup G] [DecidableEq G] in
theorem single_le_three_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) (hf : ∀ a b c, 0 ≤ f a b c) (a : α) (b : β) (c : γ) :
    f a b c ≤ ∑ x, ∑ y, ∑ z, f x y z := by
  calc
    _ ≤ ∑ z, f a b z := Finset.single_le_sum (fun z _ ↦ hf a b z) (Finset.mem_univ c)
    _ ≤ ∑ y, ∑ z, f a y z := Finset.single_le_sum
      (fun y _ ↦ Finset.sum_nonneg (fun z _ ↦ hf a y z)) (Finset.mem_univ b)
    _ ≤ _ := Finset.single_le_sum
      (fun x _ ↦ Finset.sum_nonneg (fun y _ ↦ Finset.sum_nonneg (fun z _ ↦ hf x y z)))
      (Finset.mem_univ a)

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

omit [DecidableEq G] in
theorem total_mass (Q : StationaryAdditiveLaw S ν) (hν : ∑ a, ν a = 1) :
    (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d) = 1 := by simp_rw [Q.first]; exact hν

omit [DecidableEq G] in
theorem mass_le_endpoints (Q : StationaryAdditiveLaw S ν) (a b c d : S) :
    Q.mass a b c d ≤ ν a ∧ Q.mass a b c d ≤ ν b ∧
    Q.mass a b c d ≤ ν c ∧ Q.mass a b c d ≤ ν d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Q.first a]
    exact single_le_three_sum _ (Q.nonneg a) b c d
  · rw [← Q.second b]
    exact single_le_three_sum _ (fun x y z ↦ Q.nonneg x b y z) a c d
  · rw [← Q.third c]
    exact single_le_three_sum _ (fun x y z ↦ Q.nonneg x y c z) a b d
  · rw [← Q.fourth d]
    exact single_le_three_sum _ (fun x y z ↦ Q.nonneg x y z d) a b c

omit [DecidableEq G] in
theorem positive_endpoints (Q : StationaryAdditiveLaw S ν) {a b c d : S}
    (h : Q.mass a b c d ≠ 0) : 0 < ν a ∧ 0 < ν b ∧ 0 < ν c ∧ 0 < ν d := by
  have hp := lt_of_le_of_ne (Q.nonneg a b c d) (Ne.symm h)
  obtain ⟨ha, hb, hc, hd⟩ := Q.mass_le_endpoints a b c d
  exact ⟨hp.trans_le ha, hp.trans_le hb, hp.trans_le hc, hp.trans_le hd⟩

def entropy (Q : StationaryAdditiveLaw S ν) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Real.negMulLog (Q.mass a b c d)

/-- The literal unnormalized square-root-marginal reference weight. -/
def referenceWeight (ν : S → ℝ) (a b c d : S) : ℝ :=
  additiveQuadrupleWeight S (fun x ↦ Real.sqrt (ν x)) a b c d

theorem referenceWeight_nonneg (a b c d : S) :
    0 ≤ referenceWeight ν a b c d := by
  unfold referenceWeight additiveQuadrupleWeight
  split_ifs <;> positivity

theorem referenceWeight_pos (Q : StationaryAdditiveLaw S ν) {a b c d : S}
    (h : Q.mass a b c d ≠ 0) : 0 < referenceWeight ν a b c d := by
  obtain ⟨ha, hb, hc, hd⟩ := Q.positive_endpoints h
  have he : a.val + b.val = c.val + d.val := by
    by_contra hh
    exact h (Q.supported a b c d hh)
  simp only [referenceWeight, additiveQuadrupleWeight, if_pos he]
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb))
    (mul_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd))

theorem referenceWeight_log_term (Q : StationaryAdditiveLaw S ν) (a b c d : S) :
    Q.mass a b c d * Real.log (referenceWeight ν a b c d) =
      Q.mass a b c d * (Real.log (ν a) + Real.log (ν b) + Real.log (ν c) + Real.log (ν d)) / 2 := by
  by_cases h : Q.mass a b c d = 0
  · simp [h]
  obtain ⟨ha, hb, hc, hd⟩ := Q.positive_endpoints h
  have he : a.val + b.val = c.val + d.val := by
    by_contra hh
    exact h (Q.supported a b c d hh)
  simp only [referenceWeight, additiveQuadrupleWeight, if_pos he]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt ha.le, Real.log_sqrt hb.le, Real.log_sqrt hc.le, Real.log_sqrt hd.le]
  ring

end StationaryAdditiveLaw

/-- The previously constructed exact-optimizer law is an instance of
the general stationary additive law, with no extra marginal assumptions. -/
def optimizerStationaryAdditiveLaw {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    StationaryAdditiveLaw S (fun x ↦ f x ^ 2) where
  mass := optimizerQuadrupleLaw S f
  nonneg := optimizerQuadrupleLaw_nonneg hf
  supported := by
    intro a b c d h
    simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, h]
  first := optimizerQuadrupleLaw_first_marginal hS hf hE
  second := optimizerQuadrupleLaw_second_marginal hS hf hE
  third := optimizerQuadrupleLaw_third_marginal hS hf hE
  fourth := optimizerQuadrupleLaw_fourth_marginal hS hf hE

end
end Erdos539Geometry
