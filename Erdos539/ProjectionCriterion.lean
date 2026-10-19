/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.OrthantAnchor
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- The proposed joint projection condition is explicitly a hypothesis, not
an assertion that the stronger unrestricted conjecture has been established. -/
def JointProjectionHypothesis (A B η : ℝ) : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (S : Finset (Fin d → ℝ)), S.Nonempty →
    ∀ (K : ℝ), 1 ≤ K → ((differences S).card : ℝ) ≤ K * S.card →
      (∏ i : Fin d, ((S.image (lineProjection i)).card : ℝ)) ≤
        Real.exp (A * (d : ℝ) ^ 2) * K ^ (B * d) *
          (maxFan S : ℝ) ^ (2 * d - 1 - η)

/-- A bounded dimensional and doubling cost with a 1/d exponent gain. -/
def UniformLogGainHypothesis (U V c : ℝ) : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (S : Finset (Fin d → ℝ)), S.Nonempty →
    ∀ (K : ℝ), 1 ≤ K → ((differences S).card : ℝ) ≤ K * S.card →
      (1 / 2 + c / d) * Real.log S.card - U * d - V * Real.log K ≤ Real.log (maxFan S)

/-- The scalar implication preserves a dimension-independent doubling cost. -/
theorem projection_criterion_scalar {d A B η X Y Q : ℝ}
    (hd : 1 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B) (_hη : 0 < η) (hη1 : η ≤ 1)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : d * X ≤ d * Real.log d + A * d ^ 2 + B * d * Y + (2 * d - η) * Q) :
    (1 / 2 + (η / 4) / d) * X - (A + 1) * d - B * Y ≤ Q := by
  have hd0 : 0 < d := by linarith
  have hden : 0 < 2 * d - η := by linarith
  have hlog : Real.log d ≤ d := by linarith [Real.log_le_sub_one_of_pos hd0]
  have hgain : (1 / 2 + (η / 4) / d) * (2 * d - η) ≤ d := by
    apply (mul_le_mul_iff_of_pos_right hd0).mp
    field_simp
    nlinarith [sq_nonneg η]
  have hgainX := mul_le_mul_of_nonneg_right hgain hX
  have hcost : d * Real.log d + A * d ^ 2 ≤ (2 * d - η) * ((A + 1) * d) := by
    have h1 := mul_le_mul_of_nonneg_left hlog hd0.le
    have h2 := mul_le_mul_of_nonneg_right (show d ≤ 2 * d - η by linarith)
      (show 0 ≤ (A + 1) * d by positivity)
    nlinarith
  have hcostK := mul_le_mul_of_nonneg_right (show d ≤ 2 * d - η by linarith) (mul_nonneg hB hY)
  apply (mul_le_mul_iff_of_pos_right hden).mp
  nlinarith

/-- The exact orthant-anchor bound converts the proposed joint projection
estimate into the uniform gain needed by weak PFR. -/
theorem JointProjectionHypothesis.uniformLogGain {A B η : ℝ}
    (hproj : JointProjectionHypothesis A B η) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : 0 < η) (hη1 : η ≤ 1) : UniformLogGainHypothesis (A + 1) B (η / 4) := by
  intro d hd S hS K hK hD
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hM : (0 : ℝ) < maxFan S := by exact_mod_cast one_le_maxFan hS
  have hK0 : 0 < K := by linarith
  let P : ℝ := ∏ i : Fin d, ((S.image (lineProjection i)).card : ℝ)
  have hP : 0 < P := Finset.prod_pos (fun i _ ↦ by exact_mod_cast (hS.image (lineProjection i)).card_pos)
  obtain ⟨a, ha, hcount⟩ := exists_orthant_anchor hS (by simpa only [Fintype.card_fin] using hd)
  have hc := hcount.trans (Nat.mul_le_mul_left _ (card_fan_le_maxFan ha))
  simp only [Fintype.card_fin] at hc
  have hcR : (S.card : ℝ) ^ d ≤ (d : ℝ) ^ d * P * maxFan S := by
    dsimp only [P]
    exact_mod_cast hc
  have hcl := Real.log_le_log (pow_pos hn d) hcR
  rw [Real.log_mul (mul_pos (pow_pos hdR d) hP).ne' hM.ne',
    Real.log_mul (pow_pos hdR d).ne' hP.ne', Real.log_pow, Real.log_pow] at hcl
  have hbudget := hproj d hd S hS K hK hD
  have hbl := Real.log_le_log hP hbudget
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hK0 _)).ne'
      (Real.rpow_pos_of_pos hM _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hK0 _).ne',
    Real.log_exp, Real.log_rpow hK0, Real.log_rpow hM] at hbl
  apply projection_criterion_scalar (by exact_mod_cast hd) hA hB hη hη1
    (Real.log_natCast_nonneg _) (Real.log_nonneg hK)
  have hh : Real.log P ≤ A * (d : ℝ) ^ 2 + (B * d) * Real.log K +
      (2 * d - 1 - η) * Real.log (maxFan S) := hbl
  nlinarith

end
end Erdos539Geometry
