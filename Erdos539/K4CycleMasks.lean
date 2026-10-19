/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.K4CycleSharpness

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- The range is exactly the binary even-degree edge configurations of K4. -/
theorem k4CycleEncode_range : ∀ y : Fin 6 → Bool,
    (∃ x, k4CycleEncode x = y) ↔
      (((y 0 ^^ y 1) ^^ y 2 = false) ∧ ((y 0 ^^ y 3) ^^ y 4 = false) ∧
       ((y 1 ^^ y 3) ^^ y 5 = false) ∧ ((y 2 ^^ y 4) ^^ y 5 = false)) := by
  decide +kernel

def k4CycleMaskEntropy (I : Finset (Fin 6)) : ℝ :=
  finiteEntropy (finitePush (finiteUniformWeight CycleBits) (fun x (i : I) ↦ k4CycleEncode x i.val))

theorem k4CycleMaskEntropy_star (v : Fin 4) :
    k4CycleMaskEntropy (k4Star ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v) = 2 * Real.log 2 := by
  have he : k4CycleMaskEntropy (k4Star ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v) =
      finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleStar v)) := by
    apply finiteEntropy_push_eq_of_fibers _ (finiteUniformWeight_nonneg _)
    intro x y
    rw [k4CycleStar_fibers]
    constructor
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
    · intro h
      funext i
      exact h i.val i.property
  rw [he, k4Cycle_star_entropy]

theorem k4CycleMaskEntropy_triangle (v : Fin 4) :
    k4CycleMaskEntropy (k4Triangle ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v) = 3 * Real.log 2 := by
  have he : k4CycleMaskEntropy (k4Triangle ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v) =
      finiteEntropy (finitePush (finiteUniformWeight CycleBits) (k4CycleTriangle v)) := by
    apply finiteEntropy_push_eq_of_fibers _ (finiteUniformWeight_nonneg _)
    intro x y
    rw [k4CycleTriangle_fibers]
    constructor
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
    · intro h
      funext i
      exact h i.val i.property
  rw [he, k4Cycle_triangle_entropy]

theorem k4CycleMaskEntropy_univ : k4CycleMaskEntropy Finset.univ = 3 * Real.log 2 := by
  unfold k4CycleMaskEntropy
  rw [finiteEntropy_push_eq_of_support_injective _ _ (by
    intro x y _ _ h
    apply k4CycleEncode_injective
    funext i
    exact congrFun h ⟨i, Finset.mem_univ i⟩)]
  exact cycleBits_entropy

/-- Sharpness on the literal six physical edge observations of one law. -/
theorem k4CycleMaskEntropy_coefficient_optimal {c : ℝ} (hc : c < 3) :
    c * ((1 / 2 : ℝ) * (∑ v, k4CycleMaskEntropy
      (k4Star ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v)) - k4CycleMaskEntropy Finset.univ) <
      (1 / 2 : ℝ) * (∑ v, k4CycleMaskEntropy
      (k4Triangle ({0} : Finset (Fin 6)) {1} {2} {3} {4} {5} v)) - k4CycleMaskEntropy Finset.univ := by
  simp only [k4CycleMaskEntropy_star, k4CycleMaskEntropy_triangle, k4CycleMaskEntropy_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := mul_lt_mul_of_pos_right hc (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  norm_num only [Nat.cast_ofNat]
  nlinarith

end
end Erdos539Geometry
