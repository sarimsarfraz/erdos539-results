/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedLifting

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- Full differences permit the second endpoint to depend on the vertical
output. The orientation still stays fixed throughout the lift. -/
theorem sum_card_signedRestrictedFan_le_posDiff
    (b : Bool) (F : Finset (ι → ℝ)) (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (W : Finset (ι → ℝ)) (r s : (ι → ℝ) → (ι → ℝ))
    (hr : ∀ w ∈ W, r w ∈ F ∧ s w ∈ F ∧ project I (r w) = project I (s w) ∧ signedPdiff b (r w) (s w) = w) :
    ∑ w ∈ W, (signedRestrictedFan b F J (r w)).card ≤ (posDiff F).card := by
  let S := W.sigma (fun w ↦ signedRestrictedFan b F J (r w))
  let g : (Σ _ : ι → ℝ, ι → ℝ) → (ι → ℝ) := fun z ↦ z.2 + z.1
  have hzfirst (w : ι → ℝ) (hw : w ∈ W) : ∀ i ∈ I, w i = 0 := by
    intro i hi
    rw [← (hr w hw).2.2.2]
    have he := congrFun (hr w hw).2.2.1 ⟨i, hi⟩
    change r w i = s w i at he
    cases b <;> simp [signedPdiff, pdiff, he]
  have hmaps : ∀ z ∈ S, g z ∈ posDiff F := by
    intro z hz
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hz
    obtain ⟨x, hx, hxu⟩ := mem_signedFan.mp hu
    have hlift := signedPdiff_lift b hcover (hr z.1 hw).2.2.1 (mem_slice.mp hx).2
    have he : signedPdiff b x (s z.1) = g z := by
      simpa only [hxu, (hr z.1 hw).2.2.2, g] using hlift
    cases b
    · exact mem_posDiff.mpr ⟨s z.1, (hr z.1 hw).2.1, x, (mem_slice.mp hx).1, he⟩
    · exact mem_posDiff.mpr ⟨x, (mem_slice.mp hx).1, s z.1, (hr z.1 hw).2.1, he⟩
  have hinj : (S : Set (Σ _ : ι → ℝ, ι → ℝ)).InjOn g := by
    intro z hz w hw h
    obtain ⟨hz1, hz2⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hw1, hw2⟩ := Finset.mem_sigma.mp hw
    have he := add_outputs_injective hcover
      (fun i hi ↦ signedRestrictedFan_zero_on hz2 i hi)
      (fun i hi ↦ signedRestrictedFan_zero_on hw2 i hi)
      (hzfirst z.1 hz1) (hzfirst w.1 hw1) h
    have hfst : z.1 = w.1 := he.2
    have hsnd : z.2 = w.2 := he.1
    cases z
    cases w
    cases hfst
    cases hsnd
    rfl
  calc
    _ = S.card := (Finset.card_sigma _ _).symm
    _ ≤ _ := Finset.card_le_card_of_injOn g hmaps hinj

end
end Erdos539Geometry
