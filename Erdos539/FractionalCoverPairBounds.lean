/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteFractionalCover

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype κ]

/-- A coordinate missed by two masks forces their combined weight to be
at most the total cover weight minus one. -/
theorem fractional_cover_pair_weight_le (A : κ → Finset ι) (c : κ → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    {i j : κ} (hij : i ≠ j) (hmiss : ∃ x, x ∉ A i ∧ x ∉ A j) :
    c i + c j ≤ (∑ k, c k) - 1 := by
  obtain ⟨x, hxi, hxj⟩ := hmiss
  have hpoint : ∀ k, (if k = i then c i else 0) + (if k = j then c j else 0) +
      (if x ∈ A k then c k else 0) ≤ c k := by
    intro k
    by_cases hki : k = i
    · subst k; simp [hij, hxi]
    by_cases hkj : k = j
    · subst k; simp [Ne.symm hij, hxj]
    simp only [if_neg hki, if_neg hkj, zero_add]
    split
    · exact le_rfl
    · exact hc k
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ hpoint k)
  simp only [Finset.sum_add_distrib] at hh
  simp at hh
  linarith [hcover x]

/-- Four masks of total cover weight at most two, with no covering pair,
necessarily have total weight two and all four weights exactly one half.
Nonnegative weights are allowed, so padding a smaller family by zero
weights is covered by the same statement. -/
theorem four_mask_cover_weights (A : Fin 4 → Finset ι) (c : Fin 4 → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    (hr : ∑ k, c k ≤ 2) (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j) :
    (∑ k, c k = 2) ∧ ∀ k, c k = 1 / 2 := by
  have h01 := fractional_cover_pair_weight_le A c hc hcover (by decide : (0 : Fin 4) ≠ 1) (hmiss 0 1 (by decide))
  have h02 := fractional_cover_pair_weight_le A c hc hcover (by decide : (0 : Fin 4) ≠ 2) (hmiss 0 2 (by decide))
  have h03 := fractional_cover_pair_weight_le A c hc hcover (by decide : (0 : Fin 4) ≠ 3) (hmiss 0 3 (by decide))
  have h12 := fractional_cover_pair_weight_le A c hc hcover (by decide : (1 : Fin 4) ≠ 2) (hmiss 1 2 (by decide))
  have h13 := fractional_cover_pair_weight_le A c hc hcover (by decide : (1 : Fin 4) ≠ 3) (hmiss 1 3 (by decide))
  have h23 := fractional_cover_pair_weight_le A c hc hcover (by decide : (2 : Fin 4) ≠ 3) (hmiss 2 3 (by decide))
  have hsum : (∑ k, c k) = c 0 + c 1 + c 2 + c 3 := by simp [Fin.sum_univ_succ]; ring
  have htotal : ∑ k, c k = 2 := by linarith
  refine ⟨htotal, ?_⟩
  intro k
  fin_cases k
  · change c 0 = 1 / 2; linarith
  · change c 1 = 1 / 2; linarith
  · change c 2 = 1 / 2; linarith
  · change c 3 = 1 / 2; linarith

/-- A proper cover on a nonempty coordinate universe with at most four
masks and no covering pair must actually use four masks. -/
theorem small_mask_cover_card [Nonempty ι] {m : ℕ} (hm : m ≤ 4)
    (A : Fin m → Finset ι) (c : Fin m → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hproper : ∀ k, ∃ x, x ∉ A k)
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    (hr : ∑ k, c k ≤ 2) (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j) : m = 4 := by
  have hmCases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hmCases with rfl | rfl | rfl | rfl | rfl
  · have hh := hcover (Classical.choice (inferInstance : Nonempty ι))
    norm_num at hh
  · obtain ⟨x, hx⟩ := hproper 0
    have hh := hcover x
    norm_num [hx] at hh
  · obtain ⟨x, hx, hy⟩ := hmiss 0 1 (by decide)
    have hh := hcover x
    norm_num [Fin.sum_univ_succ, hx, hy] at hh
  · have h01 := fractional_cover_pair_weight_le A c hc hcover (by decide : (0 : Fin 3) ≠ 1) (hmiss 0 1 (by decide))
    have h02 := fractional_cover_pair_weight_le A c hc hcover (by decide : (0 : Fin 3) ≠ 2) (hmiss 0 2 (by decide))
    have h12 := fractional_cover_pair_weight_le A c hc hcover (by decide : (1 : Fin 3) ≠ 2) (hmiss 1 2 (by decide))
    have hsum : (∑ k, c k) = c 0 + c 1 + c 2 := by simp [Fin.sum_univ_succ]; ring
    linarith
  · rfl

/-- Full numerical classification through four masks, including the
exclusion of families with fewer than four positive members. -/
theorem small_mask_cover_weights [Nonempty ι] {m : ℕ} (hm : m ≤ 4)
    (A : Fin m → Finset ι) (c : Fin m → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hproper : ∀ k, ∃ x, x ∉ A k)
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    (hr : ∑ k, c k ≤ 2) (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j) :
    m = 4 ∧ (∑ k, c k = 2) ∧ ∀ k, c k = 1 / 2 := by
  have hm4 := small_mask_cover_card hm A c hc hproper hcover hr hmiss
  subst m
  exact ⟨rfl, four_mask_cover_weights A c hc hcover hr hmiss⟩

end
end Erdos539Geometry
