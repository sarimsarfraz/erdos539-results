/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedFans
import Erdos539.SliceBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

def signVector (b : Bool) (x : ι → ℝ) : ι → ℝ := if b then x else -x

def signSet (b : Bool) (F : Finset (ι → ℝ)) : Finset (ι → ℝ) := F.image (signVector b)

theorem signVector_involutive (b : Bool) : Function.Involutive (signVector (ι := ι) b) := by
  intro x
  cases b <;> simp [signVector]

theorem signSet_card (b : Bool) (F : Finset (ι → ℝ)) : (signSet b F).card = F.card := by
  apply Finset.card_image_of_injective
  exact (signVector_involutive b).injective

theorem pdiff_signVector (b : Bool) (x y : ι → ℝ) :
    pdiff (signVector b x) (signVector b y) = signedPdiff b x y := by
  cases b
  · funext i
    simp [signVector, signedPdiff, pdiff, sub_eq_add_neg, add_comm]
  · rfl

theorem project_signVector_inj (b : Bool) (I : Finset ι) (x y : ι → ℝ) :
    project I (signVector b x) = project I (signVector b y) ↔ project I x = project I y := by
  cases b
  · constructor
    · intro h
      funext i
      have hi := congrFun h i
      change -x i.val = -y i.val at hi
      exact neg_injective hi
    · intro h
      funext i
      have hi := congrFun h i
      change -x i.val = -y i.val
      exact congrArg Neg.neg hi
  · rfl

theorem restrictedFan_signSet (b : Bool) (F : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ) :
    restrictedFan (signSet b F) I (signVector b a) = signedRestrictedFan b F I a := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, he⟩ := mem_fan.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (mem_slice.mp hx).1
    have hp := (project_signVector_inj b I u a).mp (mem_slice.mp hx).2
    apply mem_signedFan.mpr
    exact ⟨u, mem_slice.mpr ⟨hu, hp⟩, (pdiff_signVector b u a).symm.trans he⟩
  · intro hz
    obtain ⟨x, hx, he⟩ := mem_signedFan.mp hz
    apply mem_fan.mpr
    refine ⟨signVector b x, mem_slice.mpr ⟨Finset.mem_image_of_mem _ (mem_slice.mp hx).1,
      (project_signVector_inj b I x a).mpr (mem_slice.mp hx).2⟩, ?_⟩
    exact (pdiff_signVector b x a).trans he

/-- Reflection turns a reverse fan into an ordinary forward fan without
changing cardinalities or the coordinate conditioning. -/
theorem maxSignedRestrictedFan_eq_reflection (b : Bool) (F : Finset (ι → ℝ)) (I : Finset ι) :
    maxSignedRestrictedFan b F I = maxRestrictedFan (signSet b F) I := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    rw [← restrictedFan_signSet]
    exact card_restrictedFan_le_max I (Finset.mem_image_of_mem _ ha)
  · apply Finset.sup_le
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    rw [restrictedFan_signSet]
    exact card_signedRestrictedFan_le_max b I hx

theorem projection_signSet_card (b : Bool) (F : Finset (ι → ℝ)) (I : Finset ι) :
    (projection (signSet b F) I).card = (projection F I).card := by
  classical
  have he : projection (signSet b F) I = signSet b (projection F I) := by
    ext z
    simp only [projection, signSet, Finset.mem_image]
    constructor
    · rintro ⟨v, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨project I x, ⟨x, hx, rfl⟩, ?_⟩
      cases b <;> rfl
    · rintro ⟨v, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨signVector b x, ⟨x, hx, rfl⟩, ?_⟩
      cases b <;> rfl
  rw [he, signSet_card]

theorem one_le_maxSignedRestrictedFan (b : Bool) {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    1 ≤ maxSignedRestrictedFan b F I := by
  rw [maxSignedRestrictedFan_eq_reflection]
  exact one_le_maxRestrictedFan (hF.image (signVector b)) I

/-- Any uniform forward-fan bound also holds in the reflected direction,
with the same fixed-parent projection counts. -/
theorem restricted_signed_log_bound_of_slice_bound (b : Bool) {A S : Finset (ι → ℝ)}
    (hAS : A ⊆ S) (hA : A.Nonempty) (I J : Finset ι)
    (hcover : ∀ i, i ∈ I ∨ i ∈ J) (e c : ℝ) (he : 0 ≤ e)
    (hbound : ∀ F : Finset (J → ℝ), F.Nonempty → e * Real.log F.card - c ≤ Real.log (maxFan F)) :
    e * (Real.log A.card - Real.log (projection S I).card) - c ≤ Real.log (maxSignedRestrictedFan b A I) := by
  have hsub : signSet b A ⊆ signSet b S := Finset.image_subset_image hAS
  have h := restricted_log_bound_of_slice_bound hsub (hA.image (signVector b)) I J hcover e c he hbound
  rwa [signSet_card, projection_signSet_card, ← maxSignedRestrictedFan_eq_reflection] at h

end
end Erdos539Geometry
