/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PrefixTreeBasics
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

namespace Erdos539Geometry
noncomputable section
open scoped Finset Pointwise Classical

/-- The elementary ordered-line sumset bound, with an explicit disjoint
union below and above the sum of an extreme pair. -/
theorem real_sumset_card_lower {A B : Finset ℝ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card ≤ (A + B).card + 1 := by
  let a := A.max' hA
  let b := B.min' hB
  have ha : a ∈ A := Finset.max'_mem _ _
  have hb : b ∈ B := Finset.min'_mem _ _
  let L := A.image (fun x ↦ x + b)
  let R := (B.erase b).image (fun y ↦ a + y)
  have hL : L.card = A.card := Finset.card_image_of_injective _ (fun _ _ h ↦ add_right_cancel h)
  have hR : R.card = B.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h ↦ add_left_cancel h), Finset.card_erase_of_mem hb]
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro z hzL hzR
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzL
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hzR
    obtain ⟨hne, hy⟩ := Finset.mem_erase.mp hy
    have hxa : x ≤ a := Finset.le_max' _ _ hx
    have hby : b ≤ y := Finset.min'_le _ _ hy
    have hby' : b < y := lt_of_le_of_ne hby (Ne.symm hne)
    linarith
  have hsub : L ∪ R ⊆ A + B := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_add.mpr ⟨x, hx, b, hb, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_add.mpr ⟨a, ha, y, (Finset.mem_erase.mp hy).2, rfl⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hL, hR] at hh
  have hpos := hB.card_pos
  omega

/-- The sum/difference doubling consequence used by the elementary extraction.
Its dependency is the elementary Pluennecke-Ruzsa theorem, not weak PFR. -/
theorem sumset_card_mul_le_difference_sq {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty) : (A + A).card * A.card ≤ (A - A).card ^ 2 := by
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hA A 2 0
  simp only [two_nsmul, zero_nsmul, sub_zero, Nat.add_zero] at h
  have hpos : (0 : ℚ≥0) < A.card := by exact_mod_cast hA.card_pos
  have hh := mul_le_mul_of_nonneg_right h hpos.le
  have he : ((A - A).card / (A.card : ℚ≥0)) ^ 2 * A.card * A.card = (A - A).card ^ 2 := by
    field_simp
  rw [he] at hh
  exact_mod_cast hh

theorem sumset_card_le_of_difference_doubling {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty) {K : ℝ} (hK : ((A - A).card : ℝ) ≤ K * A.card) :
    ((A + A).card : ℝ) ≤ K ^ 2 * A.card := by
  have hn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have h := sumset_card_mul_le_difference_sq hA
  have h' : ((A + A).card : ℝ) * A.card ≤ ((A - A).card : ℝ) ^ 2 := by exact_mod_cast h
  have hKN : 0 ≤ K * A.card := (Nat.cast_nonneg _).trans hK
  have hs := mul_le_mul hK hK (Nat.cast_nonneg _) hKN
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

end
end Erdos539Geometry
