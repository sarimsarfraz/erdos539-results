/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Lifting
import Erdos539.AggregatePruning

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- A direction is selected once and retained through an anchored lift. -/
def signedPdiff (b : Bool) (x y : ι → ℝ) : ι → ℝ := if b then pdiff x y else pdiff y x

def signedFan (b : Bool) (F : Finset (ι → ℝ)) (a : ι → ℝ) : Finset (ι → ℝ) :=
  F.image (fun x ↦ signedPdiff b x a)

def signedRestrictedFan (b : Bool) (F : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ) : Finset (ι → ℝ) :=
  signedFan b (slice F I a) a

def maxSignedRestrictedFan (b : Bool) (F : Finset (ι → ℝ)) (I : Finset ι) : ℕ :=
  F.sup (fun a ↦ (signedRestrictedFan b F I a).card)

def maxTwoRestrictedFan (F : Finset (ι → ℝ)) (I : Finset ι) : ℕ :=
  max (maxSignedRestrictedFan true F I) (maxSignedRestrictedFan false F I)

def maxTwoFan (F : Finset (ι → ℝ)) : ℕ := maxTwoRestrictedFan F ∅

@[simp] theorem mem_signedFan {b : Bool} {F : Finset (ι → ℝ)} {a z : ι → ℝ} :
    z ∈ signedFan b F a ↔ ∃ x ∈ F, signedPdiff b x a = z := Finset.mem_image

@[simp] theorem signedPdiff_true (x y : ι → ℝ) : signedPdiff true x y = pdiff x y := rfl
@[simp] theorem signedPdiff_false (x y : ι → ℝ) : signedPdiff false x y = pdiff y x := rfl
@[simp] theorem signedFan_true (F : Finset (ι → ℝ)) (a : ι → ℝ) : signedFan true F a = fan F a := rfl
@[simp] theorem signedRestrictedFan_true (F : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ) :
    signedRestrictedFan true F I a = restrictedFan F I a := rfl
@[simp] theorem maxSignedRestrictedFan_true (F : Finset (ι → ℝ)) (I : Finset ι) :
    maxSignedRestrictedFan true F I = maxRestrictedFan F I := rfl

@[simp] theorem signedRestrictedFan_empty (b : Bool) (F : Finset (ι → ℝ)) (a : ι → ℝ) :
    signedRestrictedFan b F ∅ a = signedFan b F a := by rw [signedRestrictedFan, slice_empty]

theorem signedRestrictedFan_mono (b : Bool) {F G : Finset (ι → ℝ)} (h : F ⊆ G)
    (I : Finset ι) (a : ι → ℝ) : signedRestrictedFan b F I a ⊆ signedRestrictedFan b G I a :=
  Finset.image_subset_image (slice_mono h I a)

theorem card_signedRestrictedFan_le_max (b : Bool) {F : Finset (ι → ℝ)}
    (I : Finset ι) {a : ι → ℝ} (ha : a ∈ F) :
    (signedRestrictedFan b F I a).card ≤ maxSignedRestrictedFan b F I :=
  Finset.le_sup (f := fun a ↦ (signedRestrictedFan b F I a).card) ha

theorem maxSignedRestrictedFan_le_two (b : Bool) (F : Finset (ι → ℝ)) (I : Finset ι) :
    maxSignedRestrictedFan b F I ≤ maxTwoRestrictedFan F I := by
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

theorem maxFan_le_maxTwoFan (F : Finset (ι → ℝ)) : maxFan F ≤ maxTwoFan F := by
  simpa only [maxSignedRestrictedFan_true, maxRestrictedFan_empty, maxTwoFan] using
    maxSignedRestrictedFan_le_two true F ∅

theorem signedFan_subset_posDiff (b : Bool) {F : Finset (ι → ℝ)} {a : ι → ℝ} (ha : a ∈ F) :
    signedFan b F a ⊆ posDiff F := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_signedFan.mp hz
  cases b
  · exact mem_posDiff.mpr ⟨a, ha, x, hx, rfl⟩
  · exact mem_posDiff.mpr ⟨x, hx, a, ha, rfl⟩

theorem maxTwoFan_le_card_posDiff (F : Finset (ι → ℝ)) : maxTwoFan F ≤ (posDiff F).card := by
  apply max_le
  all_goals
    apply Finset.sup_le
    intro a ha
    rw [signedRestrictedFan_empty]
    exact Finset.card_le_card (signedFan_subset_posDiff _ ha)

theorem exists_maxSignedRestrictedFan (b : Bool) {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    ∃ a ∈ F, maxSignedRestrictedFan b F I = (signedRestrictedFan b F I a).card := by
  obtain ⟨a, ha, hm⟩ := F.exists_max_image (fun a ↦ (signedRestrictedFan b F I a).card) hF
  exact ⟨a, ha, le_antisymm (Finset.sup_le hm) (card_signedRestrictedFan_le_max b I ha)⟩

theorem exists_maxTwoRestrictedFan {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    ∃ b : Bool, ∃ a ∈ F, maxTwoRestrictedFan F I = (signedRestrictedFan b F I a).card := by
  by_cases h : maxSignedRestrictedFan true F I ≤ maxSignedRestrictedFan false F I
  · obtain ⟨a, ha, hm⟩ := exists_maxSignedRestrictedFan false hF I
    exact ⟨false, a, ha, (max_eq_right h).trans hm⟩
  · obtain ⟨a, ha, hm⟩ := exists_maxSignedRestrictedFan true hF I
    exact ⟨true, a, ha, (max_eq_left (le_of_not_ge h)).trans hm⟩

theorem signedRestrictedFan_zero_on {b : Bool} {F : Finset (ι → ℝ)} {I : Finset ι}
    {a z : ι → ℝ} (hz : z ∈ signedRestrictedFan b F I a) (i : ι) (hi : i ∈ I) : z i = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_signedFan.mp hz
  have he := congrFun (mem_slice.mp hx).2 ⟨i, hi⟩
  change x i = a i at he
  cases b <;> simp [signedPdiff, pdiff, he]

theorem signedPdiff_lift (b : Bool) {I J : Finset ι} (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {x y a : ι → ℝ} (hya : project I y = project I a) (hxy : project J x = project J y) :
    signedPdiff b x a = signedPdiff b x y + signedPdiff b y a := by
  cases b
  · simpa only [signedPdiff_false, add_comm] using
      pdiff_lift (fun i ↦ (hcover i).symm) hxy.symm hya.symm
  · exact pdiff_lift hcover hya hxy

end
end Erdos539Geometry
