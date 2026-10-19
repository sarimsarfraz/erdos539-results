/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionBernoulliTests
import Erdos539.BernoulliSizeTail

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance reflectionSamplingIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance reflectionSamplingIndexDecidableEq (I : Finset ℤ) : DecidableEq I := Classical.decEq _
local instance reflectionSamplingBoolDecidableEq (I : Finset ℤ) : DecidableEq (I → Bool) := Classical.decEq _

def bernoulliSelection (I : Finset ℤ) (ω : I → Bool) : Finset ℤ :=
  (I.attach.filter (fun a ↦ ω a = true)).image Subtype.val

theorem bernoulliSelection_subset (I : Finset ℤ) (ω : I → Bool) : bernoulliSelection I ω ⊆ I := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
  exact b.property

theorem mem_bernoulliSelection (I : Finset ℤ) (ω : I → Bool) (a : I) :
    a.val ∈ bernoulliSelection I ω ↔ ω a = true := by
  constructor
  · intro ha
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp ha
    have hba : b = a := Subtype.ext he
    subst b
    exact (Finset.mem_filter.mp hb).2
  · intro ha
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ha⟩, rfl⟩

theorem bernoulliSelection_card (I : Finset ℤ) (ω : I → Bool) :
    ((bernoulliSelection I ω).card : ℝ) = bernoulliCount ω := by
  rw [bernoulliSelection, Finset.card_image_of_injective _ Subtype.val_injective]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, bernoulliCount, bernoulliAll, Finset.prod_singleton]
  rfl

theorem bernoulliAll_reflectionSiteBlock (I : Finset ℤ) (ω : I → Bool) {w z x : ℤ}
    (hall : ∀ i : Fin 4, reflectionTestSite w z x i ∈ I) :
    bernoulliAll (reflectionSiteBlock I w z x) ω =
      if ∀ i : Fin 4, reflectionTestSite w z x i ∈ bernoulliSelection I ω then 1 else 0 := by
  rw [bernoulliAll_eq_indicator]
  have he : (∀ a ∈ reflectionSiteBlock I w z x, ω a = true) ↔
      ∀ i : Fin 4, reflectionTestSite w z x i ∈ bernoulliSelection I ω := by
    constructor
    · intro h i
      apply (mem_bernoulliSelection I ω ⟨_, hall i⟩).mpr
      apply h
      exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    · intro h a ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).2
      apply (mem_bernoulliSelection I ω a).mp
      rw [← hi]
      exact h i
  simp only [he]

def reflectionGoodRepresentations (I S : Finset ℤ) (w z : ℤ) : Finset ℤ :=
  (goodReflectionTests I w z).filter (fun x ↦ ∀ i : Fin 4, reflectionTestSite w z x i ∈ S)

theorem reflected_representation_card_le_good_add_three {I S : Finset ℤ} (hSI : S ⊆ I)
    {w z : ℤ} (hzw : z ≠ w) :
    ((reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)).card ≤
      (reflectionGoodRepresentations I S w z).card + 3 := by
  let R := (reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)
  let P := fun x ↦ Function.Injective (reflectionTestSite w z x)
  have hRI : R ⊆ I := by
    intro x hx
    exact hSI (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have he : R.filter P = reflectionGoodRepresentations I S w z := by
    ext x
    simp only [Finset.mem_filter, reflectionGoodRepresentations, goodReflectionTests]
    change (x ∈ R ∧ P x) ↔ (x ∈ I ∧ (∀ i, reflectionTestSite w z x i ∈ I) ∧ P x) ∧
      ∀ i, reflectionTestSite w z x i ∈ S
    have hr : x ∈ R ↔ ∀ i, reflectionTestSite w z x i ∈ S := mem_reflected_representation_iff S w z x
    constructor
    · rintro ⟨hx, hp⟩
      exact ⟨⟨hRI hx, fun i ↦ hSI (hr.mp hx i), hp⟩, hr.mp hx⟩
    · rintro ⟨⟨_, _, hp⟩, hs⟩
      exact ⟨hr.mpr hs, hp⟩
  have hb : (R.filter (fun x ↦ ¬P x)).card ≤ 3 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hRI)).trans (reflectionTest_exceptional_card_le I hzw)
  have hsum := Finset.card_filter_add_card_filter_not (s := R) P
  rw [he] at hsum
  change R.card ≤ _
  omega

theorem reflectionGoodRepresentations_card (I : Finset ℤ) (ω : I → Bool) (w z : ℤ) :
    ((reflectionGoodRepresentations I (bernoulliSelection I ω) w z).card : ℝ) =
      reflectionGoodCount I w z ω := by
  unfold reflectionGoodCount
  have he (x : goodReflectionTests I w z) :=
    bernoulliAll_reflectionSiteBlock I ω (Finset.mem_filter.mp x.property).2.1
  simp_rw [he]
  rw [reflectionGoodRepresentations, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact (Finset.sum_attach _ _).symm

theorem sampled_reflected_representation_le (I : Finset ℤ) (ω : I → Bool) {w z : ℤ} (hzw : z ≠ w) :
    (((reflectedSupport (bernoulliSelection I ω) w).filter
      (fun x ↦ z - x ∈ reflectedSupport (bernoulliSelection I ω) w)).card : ℝ) ≤
      reflectionGoodCount I w z ω + 3 := by
  have h := reflected_representation_card_le_good_add_three (bernoulliSelection_subset I ω) hzw
  have hr : ((reflectionGoodRepresentations I (bernoulliSelection I ω) w z).card : ℝ) + 3 =
      reflectionGoodCount I w z ω + 3 := by rw [reflectionGoodRepresentations_card]
  rw [← hr]
  exact_mod_cast h

end
end Erdos539Geometry
