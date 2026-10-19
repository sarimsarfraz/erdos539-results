/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RestrictedPosDiff
import Erdos539.FullDifferenceLifting

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- Deleting anchors bad in both directions and retaining a common sign
converts two-sided fiber bounds to a full positive-difference bound. -/
theorem aggregate_full_difference_pruning {A : Finset (ι → ℝ)} (hA : A.Nonempty)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (ell mu : ℝ) (hell : 0 ≤ ell)
    (hfirst : ∀ B ⊆ A, A.card ≤ 2 * B.card → ell ≤ (maxTwoRestrictedFan B J : ℝ))
    (hsecond : ∀ B ⊆ A, A.card ≤ 4 * B.card → mu ≤ (maxRestrictedPosDiff B I : ℝ)) :
    ell * mu ≤ ((posDiff A).card : ℝ) := by
  classical
  let bad := A.filter (fun a ↦ ((signedRestrictedFan true A J a).card : ℝ) < ell ∧
    ((signedRestrictedFan false A J a).card : ℝ) < ell)
  have hbadsub : bad ⊆ A := Finset.filter_subset _ _
  have hn : 0 < A.card := hA.card_pos
  have hbad : 2 * bad.card < A.card := by
    by_contra h
    have hh : A.card ≤ 2 * bad.card := Nat.le_of_not_gt h
    have hbne : bad.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, a, ha, hmax⟩ := exists_maxTwoRestrictedFan hbne J
    have hlower := hfirst bad hbadsub hh
    rw [hmax] at hlower
    have hmono := Finset.card_le_card (signedRestrictedFan_mono b hbadsub J a)
    have hp : ((signedRestrictedFan b A J a).card : ℝ) < ell := by
      have hboth := (Finset.mem_filter.mp ha).2
      cases b
      · exact hboth.2
      · exact hboth.1
    exact (not_lt_of_ge (hlower.trans (by exact_mod_cast hmono))) hp
  let G := A \ bad
  have hGsub : G ⊆ A := Finset.sdiff_subset
  have hcard : G.card + bad.card = A.card := Finset.card_sdiff_add_card_eq_card hbadsub
  have hGlarge : A.card ≤ 2 * G.card := by omega
  let P := G.filter (fun a ↦ ell ≤ ((signedRestrictedFan true A J a).card : ℝ))
  have hPG : P ⊆ G := Finset.filter_subset _ _
  have hlabel : ∃ b : Bool, ∃ T : Finset (ι → ℝ), T ⊆ A ∧ A.card ≤ 4 * T.card ∧
      ∀ a ∈ T, ell ≤ ((signedRestrictedFan b A J a).card : ℝ) := by
    by_cases hP : G.card ≤ 2 * P.card
    · refine ⟨true, P, hPG.trans hGsub, by omega, ?_⟩
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    · refine ⟨false, G \ P, Finset.sdiff_subset.trans hGsub, ?_, ?_⟩
      · have hc := Finset.card_sdiff_add_card_eq_card hPG
        omega
      · intro a ha
        obtain ⟨haG, haP⟩ := Finset.mem_sdiff.mp ha
        obtain ⟨haA, habad⟩ := Finset.mem_sdiff.mp haG
        have htrue : ((signedRestrictedFan true A J a).card : ℝ) < ell := by
          apply lt_of_not_ge
          intro h
          exact haP (Finset.mem_filter.mpr ⟨haG, h⟩)
        apply le_of_not_gt
        intro hfalse
        exact habad (Finset.mem_filter.mpr ⟨haA, htrue, hfalse⟩)
  obtain ⟨b, T, hTA, hTlarge, hgood⟩ := hlabel
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, _ha, hmax⟩ := exists_maxRestrictedPosDiff hTne I
  let W := posDiff (slice T I a)
  have hW : mu ≤ (W.card : ℝ) := by
    have h := hsecond T hTA hTlarge
    rwa [hmax] at h
  have hrepr (w : ι → ℝ) (hw : w ∈ W) :
      ∃ x ∈ slice T I a, ∃ y ∈ slice T I a, signedPdiff b x y = w := by
    obtain ⟨x, hx, y, hy, he⟩ := mem_posDiff.mp hw
    cases b
    · exact ⟨y, hy, x, hx, he⟩
    · exact ⟨x, hx, y, hy, he⟩
  let r : (ι → ℝ) → (ι → ℝ) := fun w ↦
    if hw : w ∈ W then Classical.choose (hrepr w hw) else a
  have hr (w : ι → ℝ) (hw : w ∈ W) :
      r w ∈ slice T I a ∧ ∃ y ∈ slice T I a, signedPdiff b (r w) y = w := by
    dsimp only [r]
    rw [dif_pos hw]
    exact Classical.choose_spec (hrepr w hw)
  let s : (ι → ℝ) → (ι → ℝ) := fun w ↦
    if hw : w ∈ W then Classical.choose (hr w hw).2 else a
  have hs (w : ι → ℝ) (hw : w ∈ W) : s w ∈ slice T I a ∧ signedPdiff b (r w) (s w) = w := by
    dsimp only [s]
    rw [dif_pos hw]
    exact Classical.choose_spec (hr w hw).2
  have hrA (w : ι → ℝ) (hw : w ∈ W) :
      r w ∈ A ∧ s w ∈ A ∧ project I (r w) = project I (s w) ∧ signedPdiff b (r w) (s w) = w :=
    ⟨hTA (mem_slice.mp (hr w hw).1).1, hTA (mem_slice.mp (hs w hw).1).1,
      (mem_slice.mp (hr w hw).1).2.trans (mem_slice.mp (hs w hw).1).2.symm, (hs w hw).2⟩
  have hlift := sum_card_signedRestrictedFan_le_posDiff b A I J hcover W r s hrA
  calc
    ell * mu ≤ ell * (W.card : ℝ) := mul_le_mul_of_nonneg_left hW hell
    _ = ∑ _w ∈ W, ell := by simp [mul_comm]
    _ ≤ ∑ w ∈ W, ((signedRestrictedFan b A J (r w)).card : ℝ) :=
      Finset.sum_le_sum (fun w hw ↦ hgood (r w) (mem_slice.mp (hr w hw).1).1)
    _ ≤ ((posDiff A).card : ℝ) := by
      simpa only [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hlift

end
end Erdos539Geometry
