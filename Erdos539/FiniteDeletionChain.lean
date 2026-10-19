/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteLogJensen
import Mathlib.Data.Finset.Card

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- A deletion cost charged to differences of log cardinalities telescopes
exactly. Every intermediate mask stays within the original mask. -/
theorem finite_deletion_chain {ι : Type*} (r : Finset ι → ℝ) (M E : ℝ)
    (J : Finset ι) (k : ℕ) (hk : k ≤ J.card)
    (hstep : ∀ K, K ⊆ J → k < K.card →
      ∃ i ∈ K, r K - r (K.erase i) ≤
        M * (Real.log K.card - Real.log (K.erase i).card) + E) :
    ∃ I ⊆ J, I.card = k ∧
      r J - M * (Real.log J.card - Real.log k) - ((J.card : ℝ) - k) * E ≤ r I := by
  suffices ∀ n (J : Finset ι), J.card = n → k ≤ n →
      (∀ K, K ⊆ J → k < K.card → ∃ i ∈ K, r K - r (K.erase i) ≤
        M * (Real.log K.card - Real.log (K.erase i).card) + E) →
      ∃ I ⊆ J, I.card = k ∧
        r J - M * (Real.log J.card - Real.log k) - ((J.card : ℝ) - k) * E ≤ r I by
    exact this J.card J rfl hk hstep
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J hcard hk hstep
    by_cases he : k = n
    · refine ⟨J, Finset.Subset.refl J, hcard.trans he.symm, ?_⟩
      simp [hcard, he]
    · have hkn : k < J.card := by omega
      obtain ⟨i, hi, hdel⟩ := hstep J (Finset.Subset.refl J) hkn
      have hcarderase := Finset.card_erase_of_mem hi
      have hsmall : (J.erase i).card < n := by omega
      have hkerase : k ≤ (J.erase i).card := by omega
      obtain ⟨I, hIJ, hI, hret⟩ := ih (J.erase i).card hsmall (J.erase i) rfl hkerase
        (fun K hK hkc ↦ hstep K (hK.trans (Finset.erase_subset i J)) hkc)
      refine ⟨I, hIJ.trans (Finset.erase_subset i J), hI, ?_⟩
      have hJpos : 1 ≤ J.card := by omega
      have herase : ((J.erase i).card : ℝ) = (J.card : ℝ) - 1 := by
        rw [hcarderase, Nat.cast_sub hJpos, Nat.cast_one]
      rw [herase] at hdel hret
      nlinarith

/-- Each harmonic deletion charge is at most the corresponding log drop. -/
theorem inverse_le_log_card_drop {m : ℕ} (hm : 2 ≤ m) :
    (1 : ℝ) / m ≤ Real.log m - Real.log (m - 1 : ℕ) := by
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hmone : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have h := Real.log_le_sub_one_of_pos (div_pos hmone hmpos)
  rw [Real.log_div hmone.ne' hmpos.ne', Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h
  have he : ((m : ℝ) - 1) / m = 1 - 1 / m := by field_simp
  rw [he] at h
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  linarith

end
end Erdos539Geometry
