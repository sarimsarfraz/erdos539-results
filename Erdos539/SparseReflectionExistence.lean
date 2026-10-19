/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SimultaneousReflectionSampling
import Erdos539.ReflectionFailureEstimate

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance sparseReflectionIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance sparseReflectionIndexDecidableEq (I : Finset ℤ) : DecidableEq I := Classical.decEq _
local instance sparseReflectionSampleDecidableEq (I : Finset ℤ) : DecidableEq (I → Bool) := Classical.decEq _

theorem reflected_representation_centers {S : Finset ℤ} {L : ℕ}
    (hS : S ⊆ Finset.Ico 0 (L : ℤ)) {w z x : ℤ}
    (hx : x ∈ (reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)) :
    w ∈ Finset.Ico 0 (2 * (L : ℤ)) ∧ z ∈ Finset.Ico 0 (2 * (L : ℤ)) := by
  obtain ⟨hxC, hzC⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxS, hwS⟩ := Finset.mem_filter.mp hxC
  have hzS := (Finset.mem_filter.mp hzC).1
  have hxI := Finset.mem_Ico.mp (hS hxS)
  have hwI := Finset.mem_Ico.mp (hS hwS)
  have hzI := Finset.mem_Ico.mp (hS hzS)
  constructor <;> apply Finset.mem_Ico.mpr <;> omega

/-- Simultaneous size and offcentral reflection control for a finite
integer interval, from the explicit proved probability bound. -/
theorem exists_interval_reflection_set (L : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfailure : 2 * Real.exp (-((L : ℝ) * α) / 12) +
      4 * (L : ℝ) ^ 2 * Real.exp (-(α ^ 4 * L) / 48) < 1) :
    ∃ S : Finset ℤ, S ⊆ Finset.Ico 0 (L : ℤ) ∧
      (L : ℝ) * α / 2 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ 2 * ((L : ℝ) * α) ∧
      ∀ w z : ℤ, z ≠ w →
        (((reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)).card : ℝ) ≤
          2 * (α ^ 4 * L) + 3 := by
  let I : Finset ℤ := Finset.Ico 0 (L : ℤ)
  let W : Finset ℤ := Finset.Ico 0 (2 * (L : ℤ))
  have hI : I.card = L := by simp [I]
  have hW : W.card = 2 * L := by
    simp only [W, Int.card_Ico, sub_zero]
    omega
  have hf : 2 * Real.exp (-((I.card : ℝ) * α) / 12) +
      (W.card : ℝ) ^ 2 * Real.exp (-(α ^ 4 * I.card) / 48) < 1 := by
    rw [hI, hW, Nat.cast_mul, Nat.cast_ofNat]
    convert hfailure using 1
    ring
  obtain ⟨ω, hlo, hhi, hgood⟩ := exists_simultaneous_reflection_sample I W hα hα1 hf
  rw [hI] at hlo hhi hgood
  refine ⟨bernoulliSelection I ω, bernoulliSelection_subset I ω, hlo, hhi, ?_⟩
  intro w z hzw
  by_cases hw : w ∈ W
  · by_cases hz : z ∈ W
    · exact (sampled_reflected_representation_le I ω hzw).trans
        (add_le_add (hgood w hw z hz).le le_rfl)
    · have he : (reflectedSupport (bernoulliSelection I ω) w).filter
          (fun x ↦ z - x ∈ reflectedSupport (bernoulliSelection I ω) w) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hz (reflected_representation_centers (bernoulliSelection_subset I ω) hx).2
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
  · have he : (reflectedSupport (bernoulliSelection I ω) w).filter
        (fun x ↦ z - x ∈ reflectedSupport (bernoulliSelection I ω) w) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hw (reflected_representation_centers (bernoulliSelection_subset I ω) hx).1
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The source's sparse construction for every integer m>=10, with
alpha=1/m and L=m^12. The powers are simplified without asymptotic notation. -/
theorem exists_sparse_reflection_set (m : ℕ) (hm : 10 ≤ m) :
    ∃ S : Finset ℤ, S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ) ∧
      (m : ℝ) ^ 11 / 2 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ 2 * (m : ℝ) ^ 11 ∧
      ∀ w z : ℤ, z ≠ w →
        (((reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)).card : ℝ) ≤
          2 * (m : ℝ) ^ 8 + 3 := by
  have hmR : (10 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hα : 0 ≤ 1 / (m : ℝ) := by positivity
  have hα1 : 1 / (m : ℝ) ≤ 1 := (div_le_iff₀ hmp).mpr (by linarith)
  have he1 : (m : ℝ) ^ 12 * (1 / (m : ℝ)) = (m : ℝ) ^ 11 := by field_simp
  have he4 : (1 / (m : ℝ)) ^ 4 * (m : ℝ) ^ 12 = (m : ℝ) ^ 8 := by field_simp
  have hf : 2 * Real.exp (-(((m ^ 12 : ℕ) : ℝ) * (1 / (m : ℝ))) / 12) +
      4 * (((m ^ 12 : ℕ) : ℝ)) ^ 2 * Real.exp (-((1 / (m : ℝ)) ^ 4 * ((m ^ 12 : ℕ) : ℝ)) / 48) < 1 := by
    rw [Nat.cast_pow, he1, he4, ← pow_mul]
    exact reflection_failure_estimate hmR
  have h := exists_interval_reflection_set (m ^ 12) hα hα1 hf
  simpa only [Nat.cast_pow, he1, he4] using h

end
end Erdos539Geometry
