/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Erdos539.IntegerProducts
import Erdos539.IntervalExact
import Erdos539.GluingExactPositive

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

abbrev CubeCoordinate := Unit ⊕ (Unit ⊕ Unit)

def cubeBox (W : ℕ) : Finset (CubeCoordinate → ℤ) :=
  integerProduct (intervalVectors W) (integerProduct (intervalVectors W) (intervalVectors W))

/-- The actual additive model from the manuscript: (t,a,b) maps to (Mt+a,-Mt+b). -/
def cubeModelMap (M : ℤ) : (CubeCoordinate → ℤ) →ₗ[ℤ] (Unit ⊕ Unit → ℤ) where
  toFun := fun z ↦ glueVector M (z (Sum.inl ()))
    (fun _ ↦ z (Sum.inr (Sum.inl ()))) (fun _ ↦ z (Sum.inr (Sum.inr ())))
  map_add' := by
    intro x y
    funext i
    cases i <;> simp [glueVector] <;> ring
  map_smul' := by
    intro n x
    funext i
    cases i <;> simp [glueVector] <;> ring

theorem cubeModelMap_block (M t : ℤ) (x y : Unit → ℤ) :
    cubeModelMap M (Sum.elim (fun _ : Unit ↦ t) (Sum.elim x y)) = glueVector M t x y := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => cases i; rfl

theorem cubeBox_card (W : ℕ) : (cubeBox W).card = W ^ 3 := by
  rw [cubeBox, integerProduct_card, integerProduct_card, intervalVectors_card]
  ring

theorem cubeBox_posDiff_card {W : ℕ} (hW : 0 < W) :
    (integerPositiveDifferences (cubeBox W)).card = W ^ 3 := by
  rw [cubeBox, integerProduct_positiveDifferences, integerProduct_positiveDifferences,
    integerProduct_card, integerProduct_card, intervalVectors_posDiff_card_eq hW]
  ring

/-- The image of the original box is exactly the planar layered gluing. -/
theorem cubeModelMap_image (W : ℕ) (M : ℤ) :
    (cubeBox W).image (cubeModelMap M) = gluing (intervalVectors W) (intervalVectors W) W M := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerProduct.mp hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerProduct.mp hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact mem_gluing.mpr ⟨t, Finset.mem_range.mp ht, x, hx, y, hy, (cubeModelMap_block M t x y).symm⟩
  · intro hz
    obtain ⟨t, ht, x, hx, y, hy, rfl⟩ := mem_gluing.mp hz
    apply Finset.mem_image.mpr
    refine ⟨Sum.elim (fun _ : Unit ↦ (t : ℤ)) (Sum.elim x y), ?_, cubeModelMap_block M t x y⟩
    exact mem_integerProduct.mpr ⟨_, Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩,
      _, mem_integerProduct.mpr ⟨x, hx, y, hy, rfl⟩, rfl⟩

/-- The additive model is injective on the entire difference set of the box. -/
theorem cubeModelMap_injOn_differences (W : ℕ) {M : ℤ} (hM : 2 * (W : ℤ) < M) :
    Set.InjOn (cubeModelMap M) (integerDifferences (cubeBox W) : Set (CubeCoordinate → ℤ)) := by
  intro u hu v hv he
  change u ∈ integerDifferences (cubeBox W) at hu
  change v ∈ integerDifferences (cubeBox W) at hv
  rw [cubeBox, integerProduct_differences, integerProduct_differences] at hu hv
  obtain ⟨t, _ht, x, hx, rfl⟩ := mem_integerProduct.mp hu
  obtain ⟨a, ha, b, _hb, rfl⟩ := mem_integerProduct.mp hx
  obtain ⟨t', _ht', x', hx', rfl⟩ := mem_integerProduct.mp hv
  obtain ⟨a', ha', b', _hb', rfl⟩ := mem_integerProduct.mp hx'
  have hte : t = (fun _ : Unit ↦ t ()) := by funext i; cases i; rfl
  have hte' : t' = (fun _ : Unit ↦ t' ()) := by funext i; cases i; rfl
  rw [hte, hte', cubeModelMap_block, cubeModelMap_block] at he
  have hMp : 0 < M := by omega
  have hgap := differences_coordinateGap_of_diameter hM (intervalVectors_diameter W)
  obtain ⟨ht, haa, hbb⟩ := glueVector_injective_of_gap hMp hgap () ha ha' he
  have htt : t = t' := by
    funext i
    cases i
    exact ht
  rw [htt, haa, hbb]

/-- Exact image cardinalities exhibit the failure to preserve positive parts
under an additive map that is injective on all differences. -/
theorem cubeModelMap_exact_counts {W : ℕ} (hW : 0 < W) {M : ℤ}
    (hM : 2 * (W : ℤ) < M) :
    ((cubeBox W).image (cubeModelMap M)).card = W ^ 3 ∧
      (integerDifferences ((cubeBox W).image (cubeModelMap M))).card = (2 * W - 1) ^ 3 ∧
      ((integerPositiveDifferences ((cubeBox W).image (cubeModelMap M))).card : ℤ) =
        5 * (W : ℤ) ^ 2 - 6 * W + 2 := by
  rw [cubeModelMap_image]
  have hL : (0 : ℤ) ≤ W := Int.natCast_nonneg W
  have hMp : 0 < M := by omega
  have hdiam := intervalVectors_diameter W
  have hgap := coordinateGap_of_diameter hL hM hdiam
  have hI : (intervalVectors W).Nonempty := Finset.card_pos.mp (by simpa only [intervalVectors_card] using hW)
  refine ⟨?_, ?_, ?_⟩
  · rw [gluing_card _ _ hMp hgap (), intervalVectors_card]
    ring
  · rw [gluing_integerDifferences_card_eq_of_diameter _ _ hL hM hdiam (), intervalVectors_differences_card_eq]
    ring
  · rw [gluing_integerPositiveDifferences_card_eq hI hI hW hL hM hdiam hdiam () (),
      intervalVectors_posDiff_card_eq hW, intervalVectors_differences_card_eq]
    have h1 : 1 ≤ W := hW
    have h2 : 1 ≤ 2 * W := by omega
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring

/-- The same examples retain a uniform ordinary-doubling constant below eight. -/
theorem cubeModelMap_doubling_lt_eight {W : ℕ} (hW : 0 < W) {M : ℤ}
    (hM : 2 * (W : ℤ) < M) :
    (integerDifferences ((cubeBox W).image (cubeModelMap M))).card <
      8 * ((cubeBox W).image (cubeModelMap M)).card := by
  obtain ⟨hcard, hdiff, _hpos⟩ := cubeModelMap_exact_counts hW hM
  rw [hcard, hdiff]
  have hlt : 2 * W - 1 < 2 * W := by omega
  have hh := Nat.pow_lt_pow_left hlt (by decide : (3 : ℕ) ≠ 0)
  convert hh using 1
  ring

/-- A concrete member already changes the positive-difference cardinality. -/
theorem cubeModelMap_changes_positive_difference_count {M : ℤ} (hM : 8 < M) :
    (integerPositiveDifferences ((cubeBox 4).image (cubeModelMap M))).card ≠
      (integerPositiveDifferences (cubeBox 4)).card := by
  have h := (cubeModelMap_exact_counts (by decide : 0 < 4) (by norm_num; exact hM)).2.2
  have hb := cubeBox_posDiff_card (by decide : 0 < 4)
  norm_num at h hb
  omega

end
end Erdos539Geometry
