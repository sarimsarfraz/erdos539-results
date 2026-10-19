/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReferenceUniformRoot
import Mathlib.Analysis.MeanInequalities

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def powerReferenceMass {S : Finset G} (f : S → ℝ) : ℝ := ∑ x, f x ^ (4 / 3 : ℝ)
def powerReference {S : Finset G} (f : S → ℝ) (x : S) : ℝ :=
  f x ^ (4 / 3 : ℝ) / powerReferenceMass f

omit [AddCommGroup G] [DecidableEq G] in
theorem powerReferenceMass_pos {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) : 0 < powerReferenceMass f := by
  obtain ⟨a, ha⟩ := hS
  exact (Real.rpow_pos_of_pos (hf ⟨a, ha⟩) _).trans_le
    (Finset.single_le_sum (fun x _ ↦ Real.rpow_nonneg (hf x).le _) (Finset.mem_univ (⟨a, ha⟩ : S)))

omit [AddCommGroup G] [DecidableEq G] in
theorem powerReference_pos {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) (x : S) : 0 < powerReference f x :=
  div_pos (Real.rpow_pos_of_pos (hf x) _) (powerReferenceMass_pos hS hf)

omit [AddCommGroup G] [DecidableEq G] in
theorem powerReference_sum {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) : ∑ x, powerReference f x = 1 := by
  simp only [powerReference, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (powerReferenceMass_pos hS hf).ne'

omit [AddCommGroup G] [DecidableEq G] in
theorem referencePowerWeight_powerReference {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) : referencePowerWeight (powerReference f) =
      fun x ↦ (1 / powerReferenceMass f ^ (3 / 4 : ℝ)) * f x := by
  funext x
  have hc := powerReferenceMass_pos hS hf
  unfold referencePowerWeight powerReference
  rw [Real.div_rpow (Real.rpow_nonneg (hf x).le _) hc.le, ← Real.rpow_mul (hf x).le]
  norm_num
  ring

/-- The reference obtained from an arbitrary positive weight preserves
its canonical quadruple distribution, up to the explicit scalar partition. -/
theorem referencePartition_powerReference {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) :
    referencePartition S (powerReference f) = weightedGibbsPartition S f / powerReferenceMass f ^ 3 := by
  rw [referencePartition, weightedGibbsPartition, referencePowerWeight_powerReference hS hf,
    extendWeight_scale, weightedEnergy_scale]
  have hc := powerReferenceMass_pos hS hf
  rw [div_pow, one_pow, ← Real.rpow_mul_natCast hc.le]
  norm_num
  simp only [weightedGibbsPartition, div_eq_mul_inv, mul_comm]

theorem referenceDeficit_powerReference {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) :
    referenceDeficit S (powerReference f) =
      3 * Real.log (powerReferenceMass f) - Real.log (weightedGibbsPartition S f) := by
  have hc := powerReferenceMass_pos hS hf
  have hE := weightedGibbsPartition_pos hS hf
  rw [referenceDeficit, referencePartition_powerReference hS hf,
    Real.log_div hE.ne' (pow_pos hc 3).ne', Real.log_pow]
  norm_num

omit [AddCommGroup G] [DecidableEq G] in
/-- Exact Holder cardinality bound for the reference normalization. -/
theorem powerReferenceMass_cube_le_card {S : Finset G} {f : S → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hs : ∑ x, f x ^ 2 = 1) : powerReferenceMass f ^ 3 ≤ S.card := by
  have hpq : Real.HolderConjugate (3 / 2 : ℝ) 3 := by constructor <;> norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun x ↦ f x ^ (4 / 3 : ℝ)) (g := fun _ : S ↦ (1 : ℝ)) hpq
    (fun x _ ↦ Real.rpow_nonneg (hf x) _) (fun _ _ ↦ by norm_num)
  have hpower (x : S) : (f x ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) = f x ^ 2 := by
    rw [← Real.rpow_mul (hf x)]
    norm_num
  simp only [mul_one, hpower, hs, Real.one_rpow, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] at h
  have hc : 0 ≤ powerReferenceMass f := Finset.sum_nonneg (fun x _ ↦ Real.rpow_nonneg (hf x) _)
  have hh := Real.rpow_le_rpow hc h (by norm_num : (0 : ℝ) ≤ 3)
  rw [← Real.rpow_mul (Nat.cast_nonneg S.card)] at hh
  norm_num at hh
  exact hh

/-- Any normalized positive weight starts within its own cardinality /
energy budget; an exact optimizer gives log(N/Lambda) immediately. -/
theorem referenceDeficit_powerReference_le_log {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) (hs : ∑ x, f x ^ 2 = 1) :
    referenceDeficit S (powerReference f) ≤ Real.log ((S.card : ℝ) / weightedGibbsPartition S f) := by
  have hc := powerReferenceMass_pos hS hf
  have hE := weightedGibbsPartition_pos hS hf
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hl := Real.log_le_log (pow_pos hc 3) (powerReferenceMass_cube_le_card (fun x ↦ (hf x).le) hs)
  rw [Real.log_pow] at hl
  rw [referenceDeficit_powerReference hS hf, Real.log_div hN.ne' hE.ne']
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end
end Erdos539Geometry
