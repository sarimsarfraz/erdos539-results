/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedLifting

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- Remove both kinds of bad anchors before selecting a direction in the
other block. The selected direction is retained throughout the common-anchor lift. -/
theorem aggregate_two_sided_pruning {A : Finset (ι → ℝ)} (hA : A.Nonempty)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (K : Finset ι) (hKI : K ⊆ I) (hKJ : K ⊆ J)
    (ell mu : ℝ) (hell : 0 ≤ ell)
    (hfirst : ∀ b : Bool, ∀ B ⊆ A, A.card ≤ 4 * B.card → ell ≤ (maxSignedRestrictedFan b B J : ℝ))
    (hsecond : ∀ B ⊆ A, A.card ≤ 2 * B.card → mu ≤ (maxTwoRestrictedFan B I : ℝ)) :
    ell * mu ≤ (maxTwoRestrictedFan A K : ℝ) := by
  classical
  let bad := fun b : Bool ↦ A.filter (fun a ↦ ((signedRestrictedFan b A J a).card : ℝ) < ell)
  have hbadsub (b : Bool) : bad b ⊆ A := Finset.filter_subset _ _
  have hn : 0 < A.card := hA.card_pos
  have hbad (b : Bool) : 4 * (bad b).card < A.card := by
    by_contra h
    have hh : A.card ≤ 4 * (bad b).card := Nat.le_of_not_gt h
    have hbne : (bad b).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hmax⟩ := exists_maxSignedRestrictedFan b hbne J
    have hlower := hfirst b (bad b) (hbadsub b) hh
    rw [hmax] at hlower
    have hmono := Finset.card_le_card (signedRestrictedFan_mono b (hbadsub b) J a)
    have hp := (Finset.mem_filter.mp ha).2
    exact (not_lt_of_ge (hlower.trans (by exact_mod_cast hmono))) hp
  let U := bad true ∪ bad false
  have hUsub : U ⊆ A := Finset.union_subset (hbadsub true) (hbadsub false)
  have hU : 2 * U.card < A.card := by
    have hu := Finset.card_union_le (bad true) (bad false)
    have ht := hbad true
    have hf := hbad false
    dsimp only [U]
    omega
  let G := A \ U
  have hGsub : G ⊆ A := Finset.sdiff_subset
  have hcard : G.card + U.card = A.card := Finset.card_sdiff_add_card_eq_card hUsub
  have hGlarge : A.card ≤ 2 * G.card := by omega
  have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, a, ha, hmax⟩ := exists_maxTwoRestrictedFan hGne I
  let W := signedRestrictedFan b G I a
  have hW : mu ≤ (W.card : ℝ) := by
    have h := hsecond G hGsub hGlarge
    rwa [hmax] at h
  let r : (ι → ℝ) → (ι → ℝ) := fun w ↦
    if hw : w ∈ W then Classical.choose (mem_signedFan.mp hw) else a
  have hr (w : ι → ℝ) (hw : w ∈ W) : r w ∈ slice G I a ∧ signedPdiff b (r w) a = w := by
    dsimp only [r]
    rw [dif_pos hw]
    exact Classical.choose_spec (mem_signedFan.mp hw)
  have hrA (w : ι → ℝ) (hw : w ∈ W) : r w ∈ slice A I a ∧ signedPdiff b (r w) a = w :=
    ⟨slice_mono hGsub I a (hr w hw).1, (hr w hw).2⟩
  have hgood (w : ι → ℝ) (hw : w ∈ W) : ell ≤ ((signedRestrictedFan b A J (r w)).card : ℝ) := by
    have hg : r w ∈ G := (mem_slice.mp (hr w hw).1).1
    obtain ⟨hin, hnot⟩ := Finset.mem_sdiff.mp hg
    apply le_of_not_gt
    intro hbadpoint
    have hmem : r w ∈ bad b := Finset.mem_filter.mpr ⟨hin, hbadpoint⟩
    apply hnot
    cases b
    · exact Finset.mem_union_right _ hmem
    · exact Finset.mem_union_left _ hmem
  have hlift := sum_card_signedRestrictedFan_le_signedRestrictedFan b A I J hcover K hKI hKJ a W r hrA
  calc
    ell * mu ≤ ell * (W.card : ℝ) := mul_le_mul_of_nonneg_left hW hell
    _ = ∑ _w ∈ W, ell := by simp [mul_comm]
    _ ≤ ∑ w ∈ W, ((signedRestrictedFan b A J (r w)).card : ℝ) := Finset.sum_le_sum hgood
    _ ≤ ((signedRestrictedFan b A K a).card : ℝ) := by
      simpa only [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hlift
    _ ≤ (maxTwoRestrictedFan A K : ℝ) := by
      exact_mod_cast (card_signedRestrictedFan_le_max b K (hGsub ha)).trans (maxSignedRestrictedFan_le_two b A K)

end
end Erdos539Geometry
