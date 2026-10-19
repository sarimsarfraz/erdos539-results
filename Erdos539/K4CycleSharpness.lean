/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.K4BlockEntropy
import Erdos539.FiniteUniformFunctions

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

abbrev CycleBits := (Bool × Bool) × Bool

/-- The free bits give edges 12,13,23; parity determines 14,24,34. -/
def k4CycleEncode (x : CycleBits) : Fin 6 → Bool :=
  ![x.1.1, x.1.2, x.1.1 ^^ x.1.2, x.2, x.1.1 ^^ x.2, x.1.2 ^^ x.2]

def k4CycleStar (v : Fin 4) (x : CycleBits) : CycleBits :=
  match v with
  | 0 => ((x.1.1, x.1.2), x.1.1 ^^ x.1.2)
  | 1 => ((x.1.1, x.2), x.1.1 ^^ x.2)
  | 2 => ((x.1.2, x.2), x.1.2 ^^ x.2)
  | 3 => ((x.1.1 ^^ x.1.2, x.1.1 ^^ x.2), x.1.2 ^^ x.2)

def k4CycleTriangle (v : Fin 4) (x : CycleBits) : CycleBits :=
  match v with
  | 0 => ((x.2, x.1.1 ^^ x.2), x.1.2 ^^ x.2)
  | 1 => ((x.1.2, x.1.1 ^^ x.1.2), x.1.2 ^^ x.2)
  | 2 => ((x.1.1, x.1.1 ^^ x.1.2), x.1.1 ^^ x.2)
  | 3 => x

theorem k4CycleEncode_injective : Function.Injective k4CycleEncode := by decide +kernel

theorem k4CycleTriangle_injective : ∀ v, Function.Injective (k4CycleTriangle v) := by
  decide +kernel

/-- These are precisely the observations of the actual star edge masks. -/
theorem k4CycleStar_fibers : ∀ v x y, k4CycleStar v x = k4CycleStar v y ↔
    ∀ i ∈ k4Star ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v,
      k4CycleEncode x i = k4CycleEncode y i := by
  intro v
  fin_cases v <;> simp only [k4Star, Finset.mem_union, Finset.mem_singleton] <;> decide +kernel

theorem k4CycleTriangle_fibers : ∀ v x y, k4CycleTriangle v x = k4CycleTriangle v y ↔
    ∀ i ∈ k4Triangle ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v,
      k4CycleEncode x i = k4CycleEncode y i := by
  intro v
  fin_cases v <;> simp only [k4Triangle, Finset.mem_union, Finset.mem_singleton] <;> decide +kernel

/-- Each actual vertex has even edge degree. -/
theorem k4CycleStar_even : ∀ v x,
    ((k4CycleStar v x).1.1 ^^ (k4CycleStar v x).1.2) ^^ (k4CycleStar v x).2 = false := by
  decide +kernel

theorem cycleBits_entropy : finiteEntropy (finiteUniformWeight CycleBits) = 3 * Real.log 2 := by
  rw [finiteUniformWeight_entropy]
  norm_num only [Fintype.card_prod, Fintype.card_bool, Nat.cast_ofNat]
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
  norm_num

theorem k4Cycle_full_entropy :
    finiteEntropy (finitePush (finiteUniformWeight CycleBits) k4CycleEncode) = 3 * Real.log 2 := by
  rw [finiteEntropy_push_eq_of_support_injective _ _
    (fun _ _ _ _ he ↦ k4CycleEncode_injective he), cycleBits_entropy]

theorem k4Cycle_triangle_entropy (v : Fin 4) :
    finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleTriangle v)) = 3 * Real.log 2 := by
  rw [finiteEntropy_push_eq_of_support_injective _ _
    (fun _ _ _ _ he ↦ k4CycleTriangle_injective v he), cycleBits_entropy]

theorem k4Cycle_star_entropy (v : Fin 4) :
    finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleStar v)) = 2 * Real.log 2 := by
  fin_cases v <;>
    norm_num [finiteEntropy, finitePush, finiteUniformWeight, Fintype.sum_prod_type,
      Fintype.sum_bool, k4CycleStar, Real.negMulLog] <;>
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv,
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] <;> norm_num <;> ring

/-- The literal cycle-space law attains G_T=3G_S with G_S=log 2>0. -/
theorem k4Cycle_gap_values :
    ((1 / 2 : ℝ) * (∑ v, finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleStar v))) -
      finiteEntropy (finitePush (finiteUniformWeight CycleBits) k4CycleEncode) = Real.log 2) ∧
    ((1 / 2 : ℝ) * (∑ v, finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleTriangle v))) -
      finiteEntropy (finitePush (finiteUniformWeight CycleBits) k4CycleEncode) = 3 * Real.log 2) := by
  simp only [k4Cycle_star_entropy, k4Cycle_triangle_entropy, k4Cycle_full_entropy,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  constructor <;> ring

theorem k4Cycle_gap_coefficient_optimal {c : ℝ} (hc : c < 3) :
    c * ((1 / 2 : ℝ) * (∑ v, finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleStar v))) -
      finiteEntropy (finitePush (finiteUniformWeight CycleBits) k4CycleEncode)) <
    (1 / 2 : ℝ) * (∑ v, finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleTriangle v))) -
      finiteEntropy (finitePush (finiteUniformWeight CycleBits) k4CycleEncode) := by
  rw [k4Cycle_gap_values.1, k4Cycle_gap_values.2]
  exact mul_lt_mul_of_pos_right hc (Real.log_pos (by norm_num))

end
end Erdos539Geometry
