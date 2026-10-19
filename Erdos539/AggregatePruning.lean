/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Lifting
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

theorem exists_max_restrictedFan {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    ∃ a ∈ F, maxRestrictedFan F I = (restrictedFan F I a).card := by
  classical
  obtain ⟨a, ha, hm⟩ := F.exists_max_image (fun a ↦ (restrictedFan F I a).card) hF
  refine ⟨a, ha, le_antisymm ?_ (card_restrictedFan_le_max I ha)⟩
  exact Finset.sup_le hm

/-- Delete all bad anchors simultaneously, across every conditioning fiber.
The induction hypotheses quantify over subsets of the same original set `A`;
they are not separate density assumptions inside individual fibers. -/
theorem aggregate_pruning
    {A : Finset (ι → ℝ)} (hA : A.Nonempty)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (K : Finset ι) (hKI : K ⊆ I) (hKJ : K ⊆ J)
    (ell mu : ℝ) (hell : 0 ≤ ell)
    (hfirst : ∀ B ⊆ A, A.card ≤ 2 * B.card → ell ≤ (maxRestrictedFan B J : ℝ))
    (hsecond : ∀ B ⊆ A, A.card ≤ 2 * B.card → mu ≤ (maxRestrictedFan B I : ℝ)) :
    ell * mu ≤ (maxRestrictedFan A K : ℝ) := by
  classical
  let bad := A.filter (fun a ↦ ((restrictedFan A J a).card : ℝ) < ell)
  have hbadsub : bad ⊆ A := Finset.filter_subset _ _
  have hn : 0 < A.card := Finset.card_pos.mpr hA
  have hbad : 2 * bad.card < A.card := by
    by_contra h
    have hh : A.card ≤ 2 * bad.card := Nat.le_of_not_gt h
    have hbne : bad.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hmax⟩ := exists_max_restrictedFan hbne J
    have hlower := hfirst bad hbadsub hh
    rw [hmax] at hlower
    have hmono : (restrictedFan bad J a).card ≤ (restrictedFan A J a).card :=
      Finset.card_le_card (restrictedFan_mono hbadsub J a)
    have hbadpoint := (Finset.mem_filter.mp ha).2
    exact (not_lt_of_ge (hlower.trans (by exact_mod_cast hmono))) hbadpoint
  let G := A \ bad
  have hGsub : G ⊆ A := Finset.sdiff_subset
  have hcard : G.card + bad.card = A.card := Finset.card_sdiff_add_card_eq_card hbadsub
  have hGlarge : A.card ≤ 2 * G.card := by omega
  have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hmax⟩ := exists_max_restrictedFan hGne I
  let W := restrictedFan G I a
  have hW : mu ≤ (W.card : ℝ) := by
    have h := hsecond G hGsub hGlarge
    rwa [hmax] at h
  let r : (ι → ℝ) → (ι → ℝ) := fun w ↦
    if hw : w ∈ W then Classical.choose (mem_fan.mp hw) else a
  have hr (w : ι → ℝ) (hw : w ∈ W) : r w ∈ slice G I a ∧ pdiff (r w) a = w := by
    dsimp only [r]
    rw [dif_pos hw]
    exact Classical.choose_spec (mem_fan.mp hw)
  have hrA (w : ι → ℝ) (hw : w ∈ W) : r w ∈ slice A I a ∧ pdiff (r w) a = w :=
    ⟨slice_mono hGsub I a (hr w hw).1, (hr w hw).2⟩
  have hgood (w : ι → ℝ) (hw : w ∈ W) : ell ≤ ((restrictedFan A J (r w)).card : ℝ) := by
    have hg : r w ∈ G := (mem_slice.mp (hr w hw).1).1
    obtain ⟨hin, hnot⟩ := Finset.mem_sdiff.mp hg
    exact le_of_not_gt (fun h ↦ hnot (Finset.mem_filter.mpr ⟨hin, h⟩))
  have hlift := sum_card_restrictedFan_le_restrictedFan A I J hcover K hKI hKJ a W r hrA
  calc
    ell * mu ≤ ell * (W.card : ℝ) := mul_le_mul_of_nonneg_left hW hell
    _ = ∑ _w ∈ W, ell := by simp [mul_comm]
    _ ≤ ∑ w ∈ W, ((restrictedFan A J (r w)).card : ℝ) := Finset.sum_le_sum hgood
    _ ≤ ((restrictedFan A K a).card : ℝ) := by
      simpa only [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hlift
    _ ≤ (maxRestrictedFan A K : ℝ) := by exact_mod_cast card_restrictedFan_le_max K (hGsub ha)

end
end Erdos539Geometry
