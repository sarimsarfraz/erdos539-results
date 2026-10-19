/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Restricted

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- A horizontal move followed by a vertical move combines at the same anchor. -/
theorem pdiff_lift {I J : Finset ι} (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {x y a : ι → ℝ} (hya : project I y = project I a)
    (hxy : project J x = project J y) :
    pdiff x a = pdiff x y + pdiff y a := by
  funext i
  rcases hcover i with hi | hj
  · have h := congrFun hya ⟨i, hi⟩
    change y i = a i at h
    simp [pdiff, h]
  · have h := congrFun hxy ⟨i, hj⟩
    change x i = y i at h
    simp [pdiff, h]

/-- Disjointly supported outputs cannot collide when added. -/
theorem add_outputs_injective {I J : Finset ι} (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {u v u' v' : ι → ℝ}
    (hu : ∀ i ∈ J, u i = 0) (hu' : ∀ i ∈ J, u' i = 0)
    (hv : ∀ i ∈ I, v i = 0) (hv' : ∀ i ∈ I, v' i = 0)
    (h : u + v = u' + v') : u = u' ∧ v = v' := by
  have hsecond : v = v' := by
    funext i
    rcases hcover i with hi | hj
    · rw [hv i hi, hv' i hi]
    · have hh := congrFun h i
      simpa only [Pi.add_apply, hu i hj, hu' i hj, zero_add] using hh
  refine ⟨?_, hsecond⟩
  funext i
  have hh := congrFun h i
  change u i + v i = u' i + v' i at hh
  rw [hsecond] at hh
  linarith

/-- Each vertical output may select a different horizontal fiber. All lifted
outputs are still in the fan at the single original anchor `a`. -/
theorem sum_card_restrictedFan_le_restrictedFan
    (F : Finset (ι → ℝ)) (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (K : Finset ι) (hKI : K ⊆ I) (hKJ : K ⊆ J)
    (a : ι → ℝ) (W : Finset (ι → ℝ)) (r : (ι → ℝ) → (ι → ℝ))
    (hr : ∀ w ∈ W, r w ∈ slice F I a ∧ pdiff (r w) a = w) :
    ∑ w ∈ W, (restrictedFan F J (r w)).card ≤ (restrictedFan F K a).card := by
  let S := W.sigma (fun w ↦ restrictedFan F J (r w))
  let g : (Σ _ : ι → ℝ, ι → ℝ) → (ι → ℝ) := fun z ↦ z.2 + z.1
  have hzfirst (w : ι → ℝ) (hw : w ∈ W) : ∀ i ∈ I, w i = 0 := by
    intro i hi
    rw [← (hr w hw).2]
    have he := congrFun (mem_slice.mp (hr w hw).1).2 ⟨i, hi⟩
    change r w i = a i at he
    simp [pdiff, he]
  have hmaps : ∀ z ∈ S, g z ∈ restrictedFan F K a := by
    intro z hz
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hz
    obtain ⟨x, hx, hxu⟩ := mem_fan.mp hu
    apply mem_fan.mpr
    refine ⟨x, mem_slice.mpr ⟨(mem_slice.mp hx).1, ?_⟩, ?_⟩
    · funext i
      exact (congrFun (mem_slice.mp hx).2 ⟨i.val, hKJ i.property⟩).trans
        (congrFun (mem_slice.mp (hr z.1 hw).1).2 ⟨i.val, hKI i.property⟩)
    · have hlift := pdiff_lift hcover (mem_slice.mp (hr z.1 hw).1).2 (mem_slice.mp hx).2
      simpa only [hxu, (hr z.1 hw).2, g] using hlift
  have hinj : (S : Set (Σ _ : ι → ℝ, ι → ℝ)).InjOn g := by
    intro z hz w hw h
    obtain ⟨hz1, hz2⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hw1, hw2⟩ := Finset.mem_sigma.mp hw
    have he := add_outputs_injective hcover
      (fun i hi ↦ restrictedFan_zero_on hz2 i hi)
      (fun i hi ↦ restrictedFan_zero_on hw2 i hi)
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

theorem sum_card_restrictedFan_le_fan
    (F : Finset (ι → ℝ)) (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (a : ι → ℝ) (W : Finset (ι → ℝ)) (r : (ι → ℝ) → (ι → ℝ))
    (hr : ∀ w ∈ W, r w ∈ slice F I a ∧ pdiff (r w) a = w) :
    ∑ w ∈ W, (restrictedFan F J (r w)).card ≤ (fan F a).card := by
  simpa only [restrictedFan, slice_empty] using
    sum_card_restrictedFan_le_restrictedFan F I J hcover ∅
      (Finset.empty_subset I) (Finset.empty_subset J) a W r hr

end
end Erdos539Geometry
