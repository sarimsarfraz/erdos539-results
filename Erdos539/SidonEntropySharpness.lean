/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SidonQuadrupleEntropy
import Erdos539.FiniteUniformFunctions

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- Uniform measure on the six equal-unordered-pair quadruples of two labels. -/
def binarySidonQuadLaw (z : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) : ℝ :=
  if SameUnorderedPair z.1.1 z.1.2 z.2.1 z.2.2 then 1 / 6 else 0

theorem binarySidonQuadLaw_nonneg (z : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :
    0 ≤ binarySidonQuadLaw z := by unfold binarySidonQuadLaw; split_ifs <;> norm_num

theorem binarySidonQuadLaw_sum : ∑ z, binarySidonQuadLaw z = 1 := by
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, binarySidonQuadLaw, SameUnorderedPair]

theorem binarySidonQuadLaw_supported {z : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)}
    (hz : binarySidonQuadLaw z ≠ 0) : SameUnorderedPair z.1.1 z.1.2 z.2.1 z.2.2 := by
  by_contra h
  simp [binarySidonQuadLaw, h] at hz

theorem binarySidonQuadLaw_endpoint_moment (g : Fin 2 → ℝ) :
    (∑ z, binarySidonQuadLaw z * (g z.1.1 + g z.1.2 + g z.2.1 + g z.2.2)) =
      4 * ∑ x, finiteUniformWeight (Fin 2) x * g x := by
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, binarySidonQuadLaw, SameUnorderedPair, finiteUniformWeight]
  ring

theorem binarySidonQuadLaw_entropy : finiteEntropy binarySidonQuadLaw = Real.log 6 := by
  norm_num [finiteEntropy, Fintype.sum_prod_type, Fin.sum_univ_two,
    binarySidonQuadLaw, SameUnorderedPair, Real.negMulLog]
  rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- The coefficient log_2(6) is attained by the explicit two-label law. -/
theorem sidonQuadruple_entropy_sharp :
    finiteEntropy binarySidonQuadLaw = sharpSidonExponent * finiteEntropy (finiteUniformWeight (Fin 2)) := by
  rw [binarySidonQuadLaw_entropy, finiteUniformWeight_entropy]
  norm_num only [Fintype.card_fin, Nat.cast_ofNat]
  rw [sharpSidonExponent, div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]

/-- Every smaller proposed coefficient fails on this actual probability law. -/
theorem sidonQuadruple_entropy_coefficient_optimal {c : ℝ} (hc : c < sharpSidonExponent) :
    c * finiteEntropy (finiteUniformWeight (Fin 2)) < finiteEntropy binarySidonQuadLaw := by
  rw [sidonQuadruple_entropy_sharp]
  apply mul_lt_mul_of_pos_right hc
  rw [finiteUniformWeight_entropy]
  norm_num only [Fintype.card_fin, Nat.cast_ofNat]
  exact Real.log_pos (by norm_num)

end
end Erdos539Geometry
