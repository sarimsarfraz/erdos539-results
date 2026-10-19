/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedFans

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- Each vertical output may select a different horizontal fiber. All lifted
outputs are still in the fan at the single original anchor `a`. -/
theorem sum_card_signedRestrictedFan_le_signedRestrictedFan
    (b : Bool) (F : Finset (ι → ℝ)) (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (K : Finset ι) (hKI : K ⊆ I) (hKJ : K ⊆ J)
    (a : ι → ℝ) (W : Finset (ι → ℝ)) (r : (ι → ℝ) → (ι → ℝ))
    (hr : ∀ w ∈ W, r w ∈ slice F I a ∧ signedPdiff b (r w) a = w) :
    ∑ w ∈ W, (signedRestrictedFan b F J (r w)).card ≤ (signedRestrictedFan b F K a).card := by
  let S := W.sigma (fun w ↦ signedRestrictedFan b F J (r w))
  let g : (Σ _ : ι → ℝ, ι → ℝ) → (ι → ℝ) := fun z ↦ z.2 + z.1
  have hzfirst (w : ι → ℝ) (hw : w ∈ W) : ∀ i ∈ I, w i = 0 := by
    intro i hi
    rw [← (hr w hw).2]
    have he := congrFun (mem_slice.mp (hr w hw).1).2 ⟨i, hi⟩
    change r w i = a i at he
    cases b <;> simp [signedPdiff, pdiff, he]
  have hmaps : ∀ z ∈ S, g z ∈ signedRestrictedFan b F K a := by
    intro z hz
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hz
    obtain ⟨x, hx, hxu⟩ := mem_signedFan.mp hu
    apply mem_signedFan.mpr
    refine ⟨x, mem_slice.mpr ⟨(mem_slice.mp hx).1, ?_⟩, ?_⟩
    · funext i
      exact (congrFun (mem_slice.mp hx).2 ⟨i.val, hKJ i.property⟩).trans
        (congrFun (mem_slice.mp (hr z.1 hw).1).2 ⟨i.val, hKI i.property⟩)
    · have hlift := signedPdiff_lift b hcover (mem_slice.mp (hr z.1 hw).1).2 (mem_slice.mp hx).2
      simpa only [hxu, (hr z.1 hw).2, g] using hlift
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
