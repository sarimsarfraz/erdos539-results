/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedSliceBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- The largest full positive-difference set of a single coordinate fiber. -/
def maxRestrictedPosDiff (F : Finset (ι → ℝ)) (I : Finset ι) : ℕ :=
  F.sup (fun a ↦ (posDiff (slice F I a)).card)

theorem card_slice_posDiff_le_max {F : Finset (ι → ℝ)} (I : Finset ι)
    {a : ι → ℝ} (ha : a ∈ F) : (posDiff (slice F I a)).card ≤ maxRestrictedPosDiff F I :=
  Finset.le_sup (f := fun a ↦ (posDiff (slice F I a)).card) ha

theorem exists_maxRestrictedPosDiff {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    ∃ a ∈ F, maxRestrictedPosDiff F I = (posDiff (slice F I a)).card := by
  obtain ⟨a, ha, hm⟩ := F.exists_max_image (fun a ↦ (posDiff (slice F I a)).card) hF
  exact ⟨a, ha, le_antisymm (Finset.sup_le hm) (card_slice_posDiff_le_max I ha)⟩

theorem posDiff_projection_card_le (F : Finset (ι → ℝ)) (I : Finset ι) :
    (posDiff (projection F I)).card ≤ (posDiff F).card := by
  classical
  have he : posDiff (projection F I) = (posDiff F).image (project I) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_posDiff.mp hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨pdiff u v, mem_posDiff.mpr ⟨u, hu, v, hv, rfl⟩, rfl⟩
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_posDiff.mp hw
      exact mem_posDiff.mpr ⟨project I u, Finset.mem_image_of_mem _ hu,
        project I v, Finset.mem_image_of_mem _ hv, rfl⟩
  rw [he]
  exact Finset.card_image_le

theorem one_le_maxRestrictedPosDiff {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    1 ≤ maxRestrictedPosDiff F I := by
  obtain ⟨a, ha⟩ := hF
  have ha' : a ∈ slice F I a := mem_slice.mpr ⟨ha, rfl⟩
  have hzero : (0 : ι → ℝ) ∈ posDiff (slice F I a) := mem_posDiff.mpr ⟨a, ha', a, ha', pdiff_self a⟩
  exact (Finset.card_pos.mpr ⟨0, hzero⟩).trans_le (card_slice_posDiff_le_max I ha)

/-- Transfer a full positive-difference lower bound from a largest slice. -/
theorem restricted_posDiff_log_bound_of_slice_bound {A S : Finset (ι → ℝ)}
    (hAS : A ⊆ S) (hA : A.Nonempty) (I J : Finset ι)
    (hcover : ∀ i, i ∈ I ∨ i ∈ J) (e c : ℝ) (he : 0 ≤ e)
    (hbound : ∀ F : Finset (J → ℝ), F.Nonempty → e * Real.log F.card - c ≤ Real.log (posDiff F).card) :
    e * (Real.log A.card - Real.log (projection S I).card) - c ≤ Real.log (maxRestrictedPosDiff A I) := by
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
  have hq : 0 < (posDiff (projection (slice A I a) J)).card :=
    lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF)) (maxFan_le_card_posDiff _)
  have hq' : (0 : ℝ) < (posDiff (projection (slice A I a) J)).card := by exact_mod_cast hq
  have hmono := Real.log_le_log hq' (show ((posDiff (projection (slice A I a) J)).card : ℝ) ≤ maxRestrictedPosDiff A I by
    exact_mod_cast (posDiff_projection_card_le (slice A I a) J).trans (card_slice_posDiff_le_max I ha))
  have he' := mul_le_mul_of_nonneg_left (show Real.log A.card - Real.log (projection S I).card ≤
    Real.log (slice A I a).card by linarith) he
  linarith

end
end Erdos539Geometry
