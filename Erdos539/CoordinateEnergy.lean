/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MaskedEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance coordinateEnergyDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

def projectCoordinatesHom (I : Finset ι) : (ι → ℝ) →+ (I → ℝ) where
  toFun := project I
  map_zero' := rfl
  map_add' _ _ := rfl

def zeroExtendCoordinatesHom (I : Finset ι) : (I → ℝ) →+ (ι → ℝ) where
  toFun := zeroExtendCoordinates I
  map_zero' := by ext i; simp [zeroExtendCoordinates]
  map_add' x y := by
    ext i
    by_cases hi : i ∈ I <;> simp [zeroExtendCoordinates, hi]

theorem maskCoordinates_eq_self_of_zero_outside {S : Finset (ι → ℝ)} {I : Finset ι}
    (hz : ∀ x ∈ S, ∀ i ∉ I, x i = 0) {x : ι → ℝ} (hx : x ∈ S) : maskCoordinates I x = x := by
  ext i
  by_cases hi : i ∈ I
  · simp [maskCoordinates, hi]
  · simp [maskCoordinates, hi, hz x hx i hi]

theorem maskedProjection_eq_self_of_zero_outside {S : Finset (ι → ℝ)} {I : Finset ι}
    (hz : ∀ x ∈ S, ∀ i ∉ I, x i = 0) : maskedProjection S I = S := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := mem_maskedProjection.mp hx
    rwa [maskCoordinates_eq_self_of_zero_outside hz hy]
  · intro hx
    exact mem_maskedProjection.mpr ⟨x, hx, maskCoordinates_eq_self_of_zero_outside hz hx⟩

theorem project_injOn_of_zero_outside {S : Finset (ι → ℝ)} {I : Finset ι}
    (hz : ∀ x ∈ S, ∀ i ∉ I, x i = 0) : Set.InjOn (project I) S := by
  intro x hx y hy hxy
  ext i
  by_cases hi : i ∈ I
  · exact congrFun hxy ⟨i, hi⟩
  · rw [hz x hx i hi, hz y hy i hi]

/-- Zero-filled coordinates do not change the literal energy norm. -/
theorem energyNorm_projection_eq_of_zero_outside {S : Finset (ι → ℝ)} {I : Finset ι}
    (hz : ∀ x ∈ S, ∀ i ∉ I, x i = 0) : energyNorm (projection S I) = energyNorm S := by
  letI : DecidableEq (I → ℝ) := Classical.decEq _
  apply le_antisymm
  · have h := energyNorm_le_injective_image (S := projection S I) (zeroExtendCoordinatesHom I)
      (zeroExtendCoordinates_injective I).injOn
    have he : (projection S I).image (zeroExtendCoordinatesHom I) = S := by
      change (projection S I).image (zeroExtendCoordinates I) = S
      rw [← maskedProjection_eq_zeroExtend]
      exact maskedProjection_eq_self_of_zero_outside hz
    rw [he] at h
    exact h
  · have h := energyNorm_le_injective_image (projectCoordinatesHom I) (project_injOn_of_zero_outside hz)
    have he : S.image (projectCoordinatesHom I) = projection S I := by
      ext x
      simp only [Finset.mem_image, projection]
      rfl
    rw [he] at h
    exact h

@[simp] theorem project_maskCoordinates_self (I : Finset ι) (x : ι → ℝ) :
    project I (maskCoordinates I x) = project I x := by
  ext i
  simp [project, maskCoordinates]

theorem projection_maskedProjection_self (S : Finset (ι → ℝ)) (I : Finset ι) :
    projection (maskedProjection S I) I = projection S I := by
  simp only [projection, maskedProjection, Finset.image_image, Function.comp_def, project_maskCoordinates_self]

theorem energyNorm_maskedProjection_eq (S : Finset (ι → ℝ)) (I : Finset ι) :
    energyNorm (maskedProjection S I) = energyNorm (projection S I) := by
  rw [← projection_maskedProjection_self S I]
  symm
  exact energyNorm_projection_eq_of_zero_outside
    (fun _ hx _ hi ↦ maskedProjection_zero_outside hx hi)

end
end Erdos539Geometry
