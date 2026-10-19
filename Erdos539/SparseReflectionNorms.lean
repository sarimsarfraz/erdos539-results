/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionExistence
import Erdos539.EnergyNormLower

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators Pointwise
local instance sparseReflectionNormIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

theorem interval_card_sq_le_energyNorm {S : Finset ℤ} {L : ℕ}
    (hS : S.Nonempty) (hI : S ⊆ Finset.Ico 0 (L : ℤ)) :
    (S.card : ℝ) ^ 2 ≤ (2 * (L : ℝ)) * energyNorm S := by
  have hD : S - S ⊆ Finset.Ico (-(L : ℤ)) (L : ℤ) := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp ha
    have hxI := Finset.mem_Ico.mp (hI hx)
    have hyI := Finset.mem_Ico.mp (hI hy)
    apply Finset.mem_Ico.mpr
    omega
  have hd : (S - S).card ≤ 2 * L := by
    have h := Finset.card_le_card hD
    have he : (Finset.Ico (-(L : ℤ)) (L : ℤ)).card = 2 * L := by
      rw [Int.card_Ico]
      omega
    rwa [he] at h
  have hr : ((S - S).card : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hd
  exact (card_sq_le_difference_mul_energyNorm hS).trans
    (mul_le_mul_of_nonneg_right hr (energyNorm_nonneg S))

theorem sparse_reflection_parent_lower {m : ℕ} (hm : 10 ≤ m) {S : Finset ℤ}
    (hI : S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ))
    (hcard : (m : ℝ) ^ 11 / 2 ≤ (S.card : ℝ)) :
    (m : ℝ) ^ 10 / 8 ≤ energyNorm S := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hcard
  have hS : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hN)
  have hE := interval_card_sq_le_energyNorm hS hI
  rw [Nat.cast_pow] at hE
  have hsq : ((m : ℝ) ^ 11 / 2) ^ 2 ≤ (S.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcard 2
  apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ) ^ 12)).mp
  nlinarith only [hsq, hE]

theorem sparse_reflection_child_upper {m : ℕ} (hm : 10 ≤ m) {S : Finset ℤ}
    (hrepr : ∀ w z : ℤ, z ≠ w →
      (((reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)).card : ℝ) ≤
        2 * (m : ℝ) ^ 8 + 3) (w : ℤ) :
    energyNorm (reflectedSupport S w) ≤ 3 * (m : ℝ) ^ 8 := by
  have hmR : (10 : ℝ) ≤ m := by exact_mod_cast hm
  have hm8 : (10 : ℝ) ^ 8 ≤ (m : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hmR 8
  have h := reflectedSupport_energyNorm_le S w (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 8 + 3) (hrepr w)
  nlinarith

/-- Every m>=10 has one actual sparse integer support with the source's
parent norm bound and simultaneous arbitrary-weight reflected norm ratio. -/
theorem exists_sparse_reflection_norms (m : ℕ) (hm : 10 ≤ m) :
    ∃ S : Finset ℤ, S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ) ∧
      (m : ℝ) ^ 11 / 2 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ 2 * (m : ℝ) ^ 11 ∧
      (m : ℝ) ^ 10 / 8 ≤ energyNorm S ∧
      ∀ w : ℤ, energyNorm (reflectedSupport S w) ≤ 3 * (m : ℝ) ^ 8 ∧
        energyNorm (reflectedSupport S w) / energyNorm S ≤ 24 / (m : ℝ) ^ 2 := by
  obtain ⟨S, hI, hlo, hhi, hrepr⟩ := exists_sparse_reflection_set m hm
  have hp := sparse_reflection_parent_lower hm hI hlo
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnorm : 0 < energyNorm S := lt_of_lt_of_le (by positivity) hp
  refine ⟨S, hI, hlo, hhi, hp, ?_⟩
  intro w
  have hc := sparse_reflection_child_upper hm hrepr w
  refine ⟨hc, ?_⟩
  apply (div_le_div_iff₀ hnorm (pow_pos hmR 2)).mpr
  have hpp := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 24)
  have hcp := mul_le_mul_of_nonneg_right hc (pow_nonneg hmR.le 2)
  nlinarith only [hpp, hcp]

end
end Erdos539Geometry
