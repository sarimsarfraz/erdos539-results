/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafProjectionEntropy
import Erdos539.FiniteFiberCard

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem fourLeafBranch_projection_card {T : ℕ} (hT : 0 < T) (I : Finset (Fin 4)) :
    ((fourLeafBranch T).image (fun x (i : I) ↦ x i.val)).card =
      T ^ (fourLeafActiveDigits I).card := by
  have hf : Function.Surjective (fourLeafObserve T I) := by
    intro y
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp y.property
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a, Subtype.ext he⟩
  have hg : Function.Surjective (fun a : Fin 7 → Fin T ↦ fun j : fourLeafActiveDigits I ↦ a j.val) := by
    intro b
    refine ⟨fun j ↦ if hj : j ∈ fourLeafActiveDigits I then b ⟨j, hj⟩ else ⟨0, hT⟩, ?_⟩
    funext j
    simp only [dif_pos j.property]
  have h := finite_card_eq_of_same_fibers (fourLeafObserve T I)
    (fun a (j : fourLeafActiveDigits I) ↦ a j.val) hf hg (fourLeafObserve_same_fibers hT I)
  simpa using h

theorem fourLeaf_singleton_digits : ∀ i : Fin 4, (fourLeafActiveDigits {i}).card = 3 := by
  decide +kernel

theorem fourLeafBranch_coordinate_card {T : ℕ} (hT : 0 < T) (i : Fin 4) :
    ((fourLeafBranch T).image (fun x ↦ x i)).card = T ^ 3 := by
  have he : ((fourLeafBranch T).image (fun x (j : ({i} : Finset (Fin 4))) ↦ x j.val)).image
      (fun x ↦ x ⟨i, Finset.mem_singleton_self i⟩) =
        (fourLeafBranch T).image (fun x ↦ x i) := by
    rw [Finset.image_image]
    rfl
  have hi : Function.Injective (fun x : ({i} : Finset (Fin 4)) → ℤ ↦
      x ⟨i, Finset.mem_singleton_self i⟩) := by
    intro x y h
    funext j
    have hj : j = ⟨i, Finset.mem_singleton_self i⟩ := by
      apply Subtype.ext
      exact Finset.mem_singleton.mp j.property
    simpa only [hj] using h
  rw [← he, Finset.card_image_of_injective _ hi, fourLeafBranch_projection_card hT,
    fourLeaf_singleton_digits]

end
end Erdos539Geometry
