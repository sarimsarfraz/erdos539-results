/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Fibers

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}
local instance maskedProjectionDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Coordinate projection embedded back in the parent space by zero-filling.
Keeping one ambient type makes the entire candidate family finite. -/
def maskCoordinates (I : Finset ι) (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ if i ∈ I then x i else 0

def maskedProjection (S : Finset (ι → ℝ)) (I : Finset ι) : Finset (ι → ℝ) :=
  S.image (maskCoordinates I)

@[simp] theorem mem_maskedProjection {S : Finset (ι → ℝ)} {I : Finset ι} {y : ι → ℝ} :
    y ∈ maskedProjection S I ↔ ∃ x ∈ S, maskCoordinates I x = y := Finset.mem_image

@[simp] theorem maskCoordinates_add (I : Finset ι) (x y : ι → ℝ) :
    maskCoordinates I (x + y) = maskCoordinates I x + maskCoordinates I y := by
  funext i
  by_cases hi : i ∈ I <;> simp [maskCoordinates, hi]

@[simp] theorem maskCoordinates_pdiff (I : Finset ι) (x y : ι → ℝ) :
    maskCoordinates I (pdiff x y) = pdiff (maskCoordinates I x) (maskCoordinates I y) := by
  funext i
  by_cases hi : i ∈ I <;> simp [maskCoordinates, pdiff, hi]

@[simp] theorem maskCoordinates_comp (I J : Finset ι) (x : ι → ℝ) :
    maskCoordinates J (maskCoordinates I x) = maskCoordinates (I ∩ J) x := by
  funext i
  by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp [maskCoordinates, hi, hj]

@[simp] theorem maskCoordinates_univ [Fintype ι] (x : ι → ℝ) :
    maskCoordinates Finset.univ x = x := by ext i; simp [maskCoordinates]

@[simp] theorem maskCoordinates_empty (x : ι → ℝ) : maskCoordinates ∅ x = 0 := by
  ext i
  simp [maskCoordinates]

@[simp] theorem maskedProjection_univ [Fintype ι] (S : Finset (ι → ℝ)) :
    maskedProjection S Finset.univ = S := by
  have he : maskCoordinates (Finset.univ : Finset ι) = id := funext maskCoordinates_univ
  simp only [maskedProjection, he, Finset.image_id]

@[simp] theorem maskedProjection_nonempty {S : Finset (ι → ℝ)} {I : Finset ι} :
    (maskedProjection S I).Nonempty ↔ S.Nonempty := Finset.image_nonempty

@[simp] theorem maskedProjection_empty_coordinates {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    maskedProjection S ∅ = {0} := by
  have he : maskCoordinates (∅ : Finset ι) = fun _ ↦ (0 : ι → ℝ) := funext maskCoordinates_empty
  simpa only [maskedProjection, he] using Finset.image_const hS (0 : ι → ℝ)

theorem maskedProjection_mono {A S : Finset (ι → ℝ)} (hAS : A ⊆ S) (I : Finset ι) :
    maskedProjection A I ⊆ maskedProjection S I := Finset.image_subset_image hAS

theorem maskedProjection_card_le (S : Finset (ι → ℝ)) (I : Finset ι) :
    (maskedProjection S I).card ≤ S.card := Finset.card_image_le

@[simp] theorem maskedProjection_twice (S : Finset (ι → ℝ)) (I J : Finset ι) :
    maskedProjection (maskedProjection S I) J = maskedProjection S (I ∩ J) := by
  simp only [maskedProjection, Finset.image_image, Function.comp_def, maskCoordinates_comp]

theorem maskedProjection_subset_parent {S T : Finset (ι → ℝ)} {I J : Finset ι}
    (hT : T ⊆ maskedProjection S I) (hJI : J ⊆ I) :
    maskedProjection T J ⊆ maskedProjection S J := by
  have h := maskedProjection_mono hT J
  simpa only [maskedProjection_twice, Finset.inter_eq_right.mpr hJI] using h

theorem posDiff_maskedProjection (S : Finset (ι → ℝ)) (I : Finset ι) :
    posDiff (maskedProjection S I) = maskedProjection (posDiff S) I := by
  ext z
  simp only [mem_posDiff, mem_maskedProjection]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hz⟩
    exact ⟨pdiff x y, ⟨x, hx, y, hy, rfl⟩, by simpa using hz⟩
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, hz⟩
    exact ⟨maskCoordinates I x, ⟨x, hx, rfl⟩, maskCoordinates I y, ⟨y, hy, rfl⟩,
      by simpa using hz⟩

theorem posDiff_maskedProjection_card_le (S : Finset (ι → ℝ)) (I : Finset ι) :
    (posDiff (maskedProjection S I)).card ≤ (posDiff S).card := by
  rw [posDiff_maskedProjection]
  exact maskedProjection_card_le _ _

theorem maskedProjection_zero_outside {S : Finset (ι → ℝ)} {I : Finset ι}
    {x : ι → ℝ} (hx : x ∈ maskedProjection S I) {i : ι} (hi : i ∉ I) : x i = 0 := by
  obtain ⟨y, _, rfl⟩ := mem_maskedProjection.mp hx
  simp [maskCoordinates, hi]

/-- The zero-filled projection is exactly the usual coordinate projection
followed by the injective zero extension. -/
def zeroExtendCoordinates (I : Finset ι) (x : I → ℝ) : ι → ℝ :=
  fun i ↦ if h : i ∈ I then x ⟨i, h⟩ else 0

theorem zeroExtendCoordinates_injective (I : Finset ι) :
    Function.Injective (zeroExtendCoordinates I) := by
  intro x y h
  funext i
  have he := congrFun h i.val
  simpa only [zeroExtendCoordinates, dif_pos i.property] using he

@[simp] theorem zeroExtendCoordinates_project (I : Finset ι) (x : ι → ℝ) :
    zeroExtendCoordinates I (project I x) = maskCoordinates I x := by
  ext i
  by_cases hi : i ∈ I <;> simp [zeroExtendCoordinates, maskCoordinates, project, hi]

theorem maskedProjection_eq_zeroExtend (S : Finset (ι → ℝ)) (I : Finset ι) :
    maskedProjection S I = (projection S I).image (zeroExtendCoordinates I) := by
  simp only [projection, Finset.image_image, Function.comp_def, zeroExtendCoordinates_project]
  rfl

theorem maskedProjection_card_eq_projection (S : Finset (ι → ℝ)) (I : Finset ι) :
    (maskedProjection S I).card = (projection S I).card := by
  rw [maskedProjection_eq_zeroExtend]
  exact Finset.card_image_of_injective _ (zeroExtendCoordinates_injective I)

end
end Erdos539Geometry
