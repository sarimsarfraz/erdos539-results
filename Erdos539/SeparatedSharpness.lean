/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.BinaryCubeHierarchy
import Erdos539.SharpSeparatedExponents

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
local instance separatedSharpnessIntDecidableEq : DecidableEq ℤ := Classical.decEq _

theorem sharpRetentionBeta_log_identity :
    sharpRetentionBeta * Real.log (4 / 3 : ℝ) = Real.log (3 / 2 : ℝ) := by
  have hpos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  have he := sharpRetentionTau_eq_log_ratio
  rw [sharpRetentionTau_eq_beta_add_one] at he
  have hh := (eq_div_iff hpos.ne').mp he
  nlinarith

theorem sharpSeparatedExponent_log_identity :
    sharpSeparatedExponent * Real.log (3 / 2 : ℝ) = Real.log 2 := by
  have hlog : Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  have h := congrArg (fun x : ℝ ↦ x * Real.log (4 / 3 : ℝ))
    sharpRetentionBeta_mul_exponent_sub_one
  have hb := congrArg (fun x : ℝ ↦ x * sharpSeparatedExponent) sharpRetentionBeta_log_identity
  nlinarith [sharpRetentionBeta_log_identity]

theorem binary_norm_sharp_power : (3 / 2 : ℝ) ^ sharpSeparatedExponent = 2 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
    mul_comm, sharpSeparatedExponent_log_identity, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Already two singleton components force the sharp norm-power exponent. -/
theorem larger_separated_exponent_fails {r : ℝ} (hr : sharpSeparatedExponent < r) :
    energyNorm ({0, 1} : Finset ℤ) ^ r >
      energyNorm ({0} : Finset ℤ) ^ r + energyNorm ({1} : Finset ℤ) ^ r := by
  simp only [energyNorm_binary, energyNorm_singleton, Real.one_rpow]
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3 / 2) hr
  rw [binary_norm_sharp_power] at h
  norm_num at *
  exact h

/-- Cube norm and deficiency attain the sharp retention coefficient. -/
theorem binaryCube_log_retention_equality (n : ℕ) :
    Real.log (energyNorm (binaryCube n)) = sharpRetentionBeta *
      (Real.log (binaryCube n).card - Real.log (energyNorm (binaryCube n))) := by
  rw [energyNorm_binaryCube, binaryCube_card, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Real.log_pow]
  have hb := sharpRetentionBeta_log_identity
  have hl : Real.log (4 / 3 : ℝ) = Real.log 2 - Real.log (3 / 2 : ℝ) := by
    rw [← Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  rw [hl] at hb
  have hh := congrArg (fun x : ℝ ↦ (n : ℝ) * x) hb
  nlinarith only [hh]

/-- No smaller coefficient works for actual separated hierarchies, even
with an arbitrary fixed additive allowance in logarithmic norm loss. -/
theorem smaller_retention_coefficient_fails {b : ℝ} (hb : b < sharpRetentionBeta) (A : ℝ) :
    ∃ n : ℕ, ∀ T ∈ (binaryCube n).image (fun x ↦ {x}),
      Real.log (energyNorm (binaryCube n)) - Real.log (energyNorm T) >
        b * ((Real.log (binaryCube n).card - Real.log (energyNorm (binaryCube n))) -
          (Real.log T.card - Real.log (energyNorm T))) + A := by
  let gap := (sharpRetentionBeta - b) * Real.log (4 / 3 : ℝ)
  have hgap : 0 < gap := mul_pos (sub_pos.mpr hb) (Real.log_pos (by norm_num))
  obtain ⟨n, hn⟩ := exists_nat_gt (A / gap)
  have hng : A < (n : ℝ) * gap := (div_lt_iff₀ hgap).mp hn
  refine ⟨n, ?_⟩
  intro T hT
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hT
  simp only [energyNorm_singleton, Real.log_one, Finset.card_singleton, Nat.cast_one,
    sub_zero, sub_self, energyNorm_binaryCube, binaryCube_card, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow]
  have hlog : Real.log (4 / 3 : ℝ) = Real.log 2 - Real.log (3 / 2 : ℝ) := by
    rw [← Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  have hh := congrArg (fun x : ℝ ↦ (n : ℝ) * x) sharpRetentionBeta_log_identity
  dsimp [gap] at hng
  rw [hlog] at hng hh
  nlinarith only [hng, hh]

/-- The sharpness counterexample includes the literal separated hierarchy
and defeats every fixed positive multiplicative allowance. -/
theorem smaller_retention_prefactor_fails {b C : ℝ} (hb : b < sharpRetentionBeta)
    (hC : 0 < C) : ∃ n : ℕ,
      SeparatedHierarchy (binaryCube n) ((binaryCube n).image (fun x ↦ {x})) ∧
      ∀ T ∈ (binaryCube n).image (fun x ↦ {x}),
        C * energyNorm T < energyNorm (binaryCube n) *
          Real.exp (-b * Real.log ((binaryCube n).card / energyNorm (binaryCube n))) := by
  obtain ⟨n, hn⟩ := smaller_retention_coefficient_fails hb (Real.log C)
  refine ⟨n, binaryCube_singleton_hierarchy n, ?_⟩
  intro T hT
  have hl := hn T hT
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hT
  simp only [energyNorm_singleton, Finset.card_singleton, Nat.cast_one, Real.log_one,
    sub_zero, mul_one] at hl ⊢
  have hroot := energyNorm_pos (binaryCube_nonempty n)
  have hN : (0 : ℝ) < (binaryCube n).card := by exact_mod_cast (binaryCube_nonempty n).card_pos
  apply (Real.log_lt_log_iff hC (mul_pos hroot (Real.exp_pos _))).mp
  rw [Real.log_mul hroot.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_div hN.ne' hroot.ne']
  linarith

/-- A concrete two-label separated partition supplies the one-step
optimality obstruction, including its actual component norms. -/
theorem binary_partition_exponent_obstruction {r : ℝ} (hr : sharpSeparatedExponent < r) :
    SeparatedSumLabels ({0, 1} : Finset ℤ) binaryLabel ∧
      energyNorm ({0, 1} : Finset ℤ) ^ r >
        ∑ i : Fin 2, energyNorm (fiber ({0, 1} : Finset ℤ) binaryLabel i) ^ r := by
  constructor
  · intro a ha b hb c hc d hd he
    rcases binary_sum_unordered ha hb hc hd he with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact Or.inl ⟨congrArg binaryLabel hac, congrArg binaryLabel hbd⟩
    · exact Or.inr ⟨congrArg binaryLabel had, congrArg binaryLabel hbc⟩
  · have h0 : fiber ({0, 1} : Finset ℤ) binaryLabel 0 = {0} := by
      ext x
      simp [mem_fiber, binaryLabel]
      aesop
    have h1 : fiber ({0, 1} : Finset ℤ) binaryLabel 1 = {1} := by
      ext x
      simp [mem_fiber, binaryLabel]
      aesop
    rw [Fin.sum_univ_two, h0, h1]
    exact larger_separated_exponent_fails hr

end
end Erdos539Geometry
