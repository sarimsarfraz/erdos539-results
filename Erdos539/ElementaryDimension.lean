/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ElementaryExtraction
import Erdos539.CoordinateCounting
import Mathlib.Data.Fintype.EquivFin

namespace Erdos539Geometry
noncomputable section
open scoped Finset Pointwise Classical

theorem exists_elementary_dimension_subset_fin {d : ℕ} (S : Finset (Fin d → ℝ))
    (hS : S.Nonempty) {K : ℝ} (hK : 1 ≤ K)
    (hDiff : ((differences S).card : ℝ) ≤ K * S.card) :
    ∃ m : ℕ, m ≤ extractionSupport (K ^ 2) ∧ ∃ B : Finset (Fin m → ℝ), B.Nonempty ∧
      (S.card : ℝ) / (1024 * K ^ 10) ≤ B.card ∧
      (posDiff B).card ≤ (posDiff S).card ∧ (differences B).card ≤ (differences S).card := by
  have hSDiff : ((S - S).card : ℝ) ≤ K * S.card := by
    have he : S - S = differences S := by
      ext z
      simp only [Finset.mem_sub, mem_differences]
    rwa [he]
  obtain ⟨T, a, hTS, hTa, hsize, hr, hinj⟩ := exists_prefixUniform_extraction hS hK hSDiff
  letI : DecidableEq (Fin d → ℝ) := Classical.decEq _
  let I := activeCoordinates a
  letI : DecidableEq (Fin I.card → ℝ) := Classical.decEq _
  let c : Fin I.card → Fin d := fun j ↦ (I.equivFin.symm j).val
  let B := T.image (fun x ↦ x ∘ c)
  have hc : (T : Set (Fin d → ℝ)).InjOn (fun x ↦ x ∘ c) := by
    intro x hx y hy he
    apply hinj hx hy
    funext i
    have hh := congrFun he (I.equivFin i)
    simpa only [Function.comp_apply, c, Equiv.symm_apply_apply] using hh
  have hBc : B.card = T.card := Finset.card_image_of_injOn hc
  refine ⟨I.card, hr, B, hTa.nonempty.image _, by simpa only [hBc] using hsize, ?_, ?_⟩
  · change (posDiff (T.image (fun x ↦ x ∘ c))).card ≤ _
    rw [posDiff_image_comp]
    exact Finset.card_image_le.trans (Finset.card_le_card (posDiff_mono hTS))
  · change (differences (T.image (fun x ↦ x ∘ c))).card ≤ _
    rw [differences_image_comp]
    exact Finset.card_image_le.trans (Finset.card_le_card (differences_mono hTS))

/-- Elementary original-coordinate dimension reduction for arbitrary finite
coordinate types; all counting, selection, and transfer inputs are proved. -/
theorem exists_elementary_dimension_subset {ι : Type*} [Fintype ι]
    (S : Finset (ι → ℝ)) (hS : S.Nonempty) {K : ℝ} (hK : 1 ≤ K)
    (hDiff : ((differences S).card : ℝ) ≤ K * S.card) :
    ∃ m : ℕ, m ≤ extractionSupport (K ^ 2) ∧ ∃ B : Finset (Fin m → ℝ), B.Nonempty ∧
      (S.card : ℝ) / (1024 * K ^ 10) ≤ B.card ∧
      (posDiff B).card ≤ (posDiff S).card ∧ (differences B).card ≤ (differences S).card := by
  letI : DecidableEq (ι → ℝ) := Classical.decEq _
  letI : DecidableEq (Fin (Fintype.card ι) → ℝ) := Classical.decEq _
  let e := Fintype.equivFin ι
  let R := reindexRealSet e S
  have hc : R.card = S.card := reindexRealSet_card e S
  have hR : R.Nonempty := hS.image _
  have hdif : (differences R).card ≤ (differences S).card := by
    change (differences (S.image (fun x ↦ x ∘ e.symm))).card ≤ _
    rw [differences_image_comp]
    exact Finset.card_image_le
  have hpos : (posDiff R).card ≤ (posDiff S).card := by
    change (posDiff (S.image (fun x ↦ x ∘ e.symm))).card ≤ _
    rw [posDiff_image_comp]
    exact Finset.card_image_le
  have hRD : ((differences R).card : ℝ) ≤ K * R.card := by
    rw [hc]
    have hh : ((differences R).card : ℝ) ≤ (differences S).card := by exact_mod_cast hdif
    exact hh.trans hDiff
  obtain ⟨m, hm, B, hB, hsize, hp, hd⟩ := exists_elementary_dimension_subset_fin R hR hK hRD
  exact ⟨m, hm, B, hB, by simpa only [hc] using hsize, hp.trans hpos, hd.trans hdif⟩

theorem exists_elementary_integer_dimension_subset {ι : Type*} [Fintype ι]
    (F : Finset (ι → ℤ)) (hF : F.Nonempty) {K : ℝ} (hK : 1 ≤ K)
    (hDiff : ((integerDifferences F).card : ℝ) ≤ K * F.card) :
    ∃ m : ℕ, m ≤ extractionSupport (K ^ 2) ∧ ∃ B : Finset (Fin m → ℝ), B.Nonempty ∧
      (F.card : ℝ) / (1024 * K ^ 10) ≤ B.card ∧
      (posDiff B).card ≤ (integerPositiveDifferences F).card ∧
      (differences B).card ≤ (integerDifferences F).card := by
  letI : DecidableEq (ι → ℝ) := Classical.decEq _
  have hR := hF.image integerToReal
  have hD : ((differences (F.image integerToReal)).card : ℝ) ≤ K * (F.image integerToReal).card := by
    simpa only [differences_integerToReal_image_card, integerToReal_image_card] using hDiff
  obtain ⟨m, hm, B, hB, hsize, hp, hd⟩ := exists_elementary_dimension_subset _ hR hK hD
  refine ⟨m, hm, B, hB, ?_, ?_, ?_⟩
  · simpa only [integerToReal_image_card] using hsize
  · exact hp.trans_eq (realPositiveDifferences_integerToReal_image_card F)
  · simpa only [differences_integerToReal_image_card] using hd

end
end Erdos539Geometry
