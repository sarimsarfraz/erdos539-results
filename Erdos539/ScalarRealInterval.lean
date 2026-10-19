/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntervalCountingEnergy
import Erdos539.ReflectedCountingTransport
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance scalarRealIntervalDecidableEq : DecidableEq ℝ := Classical.decEq _

def scalarRealInterval (N : ℕ) : Finset ℝ := (Finset.range N).image (fun i : ℕ ↦ (i : ℝ))

theorem mem_scalarRealInterval {N : ℕ} {x : ℝ} :
    x ∈ scalarRealInterval N ↔ ∃ i : ℕ, i < N ∧ (i : ℝ) = x := by
  simp only [scalarRealInterval, Finset.mem_image, Finset.mem_range]

theorem scalarRealInterval_card (N : ℕ) : (scalarRealInterval N).card = N := by
  rw [scalarRealInterval, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

theorem scalarRealInterval_nonempty {N : ℕ} (hN : 0 < N) : (scalarRealInterval N).Nonempty :=
  ⟨0, mem_scalarRealInterval.mpr ⟨0, hN, by norm_num⟩⟩

theorem scalarRealInterval_nonneg {N : ℕ} (a : scalarRealInterval N) : 0 ≤ a.val := by
  obtain ⟨i, _, hi⟩ := mem_scalarRealInterval.mp a.property
  rw [← hi]
  positivity

theorem scalarRealInterval_lt {N : ℕ} (a : scalarRealInterval N) : a.val < N := by
  obtain ⟨i, hin, hi⟩ := mem_scalarRealInterval.mp a.property
  rw [← hi]
  exact_mod_cast hin

theorem scalarRealInterval_mono {M N : ℕ} (h : M ≤ N) : scalarRealInterval M ⊆ scalarRealInterval N := by
  intro a ha
  obtain ⟨i, hi, he⟩ := mem_scalarRealInterval.mp ha
  exact mem_scalarRealInterval.mpr ⟨i, hi.trans_le h, he⟩

def scalarRealIntervalEquiv (N : ℕ) : Fin N ≃ scalarRealInterval N :=
  Equiv.ofBijective (fun i ↦ ⟨(i.val : ℝ), mem_scalarRealInterval.mpr ⟨i.val, i.isLt, rfl⟩⟩) (by
    constructor
    · intro i j h
      apply Fin.ext
      have he : (i.val : ℝ) = (j.val : ℝ) := congrArg (fun a : scalarRealInterval N ↦ a.val) h
      exact_mod_cast he
    · intro a
      obtain ⟨i, hi, he⟩ := mem_scalarRealInterval.mp a.property
      exact ⟨⟨i, hi⟩, Subtype.ext he⟩)

theorem scalarRealInterval_sum (N : ℕ) (F : ℝ → ℝ) :
    (∑ a : scalarRealInterval N, F a.val) = ∑ i ∈ Finset.range N, F (i : ℝ) := by
  have h := (scalarRealIntervalEquiv N).sum_comp (fun a ↦ F a.val)
  change (∑ i : Fin N, F (i.val : ℝ)) = _ at h
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ F (i : ℝ)) N] at h
  exact h.symm

theorem scalarRealInterval_eq_cast_image (N : ℕ) :
    scalarRealInterval N = (scalarInterval N).image (Int.castAddHom ℝ) := by
  ext x
  rw [mem_scalarRealInterval]
  simp only [Finset.mem_image, scalarInterval, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨(i : ℤ), ⟨by omega, by exact_mod_cast hi⟩, he⟩
  · rintro ⟨i, ⟨hi, hin⟩, he⟩
    refine ⟨i.toNat, by omega, ?_⟩
    have hi' : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi
    have hr : (i.toNat : ℝ) = (i : ℝ) := by exact_mod_cast hi'
    exact hr.trans he

theorem countingEnergy_scalarRealInterval (N : ℕ) :
    countingEnergy (scalarRealInterval N) = (N : ℝ) * (2 * (N : ℝ) ^ 2 + 1) / 3 := by
  rw [scalarRealInterval_eq_cast_image, countingEnergy_image_of_sum_injective]
  · exact countingEnergy_scalarInterval N
  · intro a _ b _ h
    exact Int.cast_injective h
  · intro a _ b _ h
    exact Int.cast_injective h

end
end Erdos539Geometry
