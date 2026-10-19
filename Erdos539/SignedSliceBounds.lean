/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SliceBounds
import Erdos539.SignedFans

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- Coordinate restriction cannot increase a signed fan on a slice. -/
theorem maxSignedRestricted_projection_slice_le (b : Bool) (F : Finset (ι → ℝ))
    (I J : Finset ι) (a : ι → ℝ) :
    maxSignedRestrictedFan b (projection (slice F I a) J) ∅ ≤ maxSignedRestrictedFan b F I := by
  classical
  apply Finset.sup_le
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  rw [signedRestrictedFan_empty]
  have he : signedFan b (projection (slice F I a) J) (project J x) =
      (signedFan b (slice F I a) x).image (project J) := by
    ext z
    simp only [mem_signedFan, projection, Finset.mem_image]
    have hcomm (u v : ι → ℝ) :
        project J (signedPdiff b u v) = signedPdiff b (project J u) (project J v) := by
      cases b <;> rfl
    constructor
    · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨signedPdiff b y x, ⟨y, hy, rfl⟩, hcomm y x⟩
    · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨project J y, ⟨y, hy, rfl⟩, (hcomm y x).symm⟩
  rw [he]
  have hslice := slice_eq_of_project_eq F I (mem_slice.mp hx).2
  have he' : signedFan b (slice F I a) x = signedRestrictedFan b F I x := by
    rw [signedRestrictedFan, hslice]
  rw [he']
  exact Finset.card_image_le.trans (card_signedRestrictedFan_le_max b I (mem_slice.mp hx).1)

theorem maxTwoFan_projection_slice_le (F : Finset (ι → ℝ)) (I J : Finset ι) (a : ι → ℝ) :
    maxTwoFan (projection (slice F I a) J) ≤ maxTwoRestrictedFan F I := by
  apply max_le
  · exact (maxSignedRestricted_projection_slice_le true F I J a).trans (le_max_left _ _)
  · exact (maxSignedRestricted_projection_slice_le false F I J a).trans (le_max_right _ _)

theorem one_le_maxTwoRestrictedFan {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    1 ≤ maxTwoRestrictedFan F I :=
  (one_le_maxRestrictedFan hF I).trans (maxSignedRestrictedFan_le_two true F I)

/-- A largest slice transfers a two-sided fan lower bound to a conditioned
set, still using projection counts of the original parent. -/
theorem restricted_two_log_bound_of_slice_bound {A S : Finset (ι → ℝ)}
    (hAS : A ⊆ S) (hA : A.Nonempty) (I J : Finset ι)
    (hcover : ∀ i, i ∈ I ∨ i ∈ J) (e c : ℝ) (he : 0 ≤ e)
    (hbound : ∀ F : Finset (J → ℝ), F.Nonempty → e * Real.log F.card - c ≤ Real.log (maxTwoFan F)) :
    e * (Real.log A.card - Real.log (projection S I).card) - c ≤ Real.log (maxTwoRestrictedFan A I) := by
  obtain ⟨a, ha, havg⟩ := exists_large_slice hAS hA I
  have hs : (slice A I a).Nonempty := ⟨a, mem_slice.mpr ⟨ha, rfl⟩⟩
  have hF : (projection (slice A I a) J).Nonempty := hs.image _
  have hn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hP : (0 : ℝ) < (projection S I).card := by exact_mod_cast ((hA.mono hAS).image (project I)).card_pos
  have hslice : (0 : ℝ) < (slice A I a).card := by exact_mod_cast hs.card_pos
  have hl := Real.log_le_log hn (show (A.card : ℝ) ≤ (projection S I).card * ((slice A I a).card : ℝ) by exact_mod_cast havg)
  rw [Real.log_mul hP.ne' hslice.ne'] at hl
  have hf := hbound _ hF
  rw [projection_slice_card A I J hcover a] at hf
  have hM : (0 : ℝ) < maxTwoFan (projection (slice A I a) J) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxTwoRestrictedFan hF ∅))
  have hmono := Real.log_le_log hM (show (maxTwoFan (projection (slice A I a) J) : ℝ) ≤ maxTwoRestrictedFan A I by
    exact_mod_cast maxTwoFan_projection_slice_le A I J a)
  have he' := mul_le_mul_of_nonneg_left (show Real.log A.card - Real.log (projection S I).card ≤
    Real.log (slice A I a).card by linarith) he
  linarith

end
end Erdos539Geometry
