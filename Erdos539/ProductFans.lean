/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Fans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι κ : Type*}

def coordinateProduct (A : Finset (ι → ℝ)) (B : Finset (κ → ℝ)) : Finset (ι ⊕ κ → ℝ) :=
  (A ×ˢ B).image (fun p ↦ Sum.elim p.1 p.2)

@[simp] theorem mem_coordinateProduct {A : Finset (ι → ℝ)} {B : Finset (κ → ℝ)}
    {z : ι ⊕ κ → ℝ} :
    z ∈ coordinateProduct A B ↔ ∃ x ∈ A, ∃ y ∈ B, Sum.elim x y = z := by
  simp only [coordinateProduct, Finset.mem_image, Prod.exists, Finset.mem_product]
  aesop

theorem coordinateProduct_card (A : Finset (ι → ℝ)) (B : Finset (κ → ℝ)) :
    (coordinateProduct A B).card = A.card * B.card := by
  classical
  rw [coordinateProduct, Finset.card_image_of_injOn]
  · exact Finset.card_product A B
  · intro p _ q _ h
    apply Prod.ext
    · funext i
      exact congrFun h (Sum.inl i)
    · funext i
      exact congrFun h (Sum.inr i)

theorem pdiff_sum_elim (x x' : ι → ℝ) (y y' : κ → ℝ) :
    pdiff (Sum.elim x y) (Sum.elim x' y') = Sum.elim (pdiff x x') (pdiff y y') := by
  funext i
  cases i <;> rfl

theorem fan_coordinateProduct (A : Finset (ι → ℝ)) (B : Finset (κ → ℝ))
    (x : ι → ℝ) (y : κ → ℝ) :
    fan (coordinateProduct A B) (Sum.elim x y) = coordinateProduct (fan A x) (fan B y) := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_fan.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hw
    exact mem_coordinateProduct.mpr ⟨pdiff a x, mem_fan.mpr ⟨a, ha, rfl⟩,
      pdiff b y, mem_fan.mpr ⟨b, hb, rfl⟩, (pdiff_sum_elim a x b y).symm⟩
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hz
    obtain ⟨a', ha', rfl⟩ := mem_fan.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_fan.mp hb
    exact mem_fan.mpr ⟨Sum.elim a' b', mem_coordinateProduct.mpr ⟨a', ha', b', hb', rfl⟩,
      pdiff_sum_elim a' x b' y⟩

theorem exists_fan_eq_max {A : Finset (ι → ℝ)} (hA : A.Nonempty) :
    ∃ x ∈ A, (fan A x).card = maxFan A := by
  obtain ⟨x, hx, hmax⟩ := A.exists_max_image (fun x ↦ (fan A x).card) hA
  exact ⟨x, hx, le_antisymm (card_fan_le_maxFan hx) (Finset.sup_le hmax)⟩

theorem maxFan_coordinateProduct {A : Finset (ι → ℝ)} {B : Finset (κ → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    maxFan (coordinateProduct A B) = maxFan A * maxFan B := by
  apply le_antisymm
  · apply Finset.sup_le
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_coordinateProduct.mp hz
    rw [fan_coordinateProduct, coordinateProduct_card]
    exact Nat.mul_le_mul (card_fan_le_maxFan hx) (card_fan_le_maxFan hy)
  · obtain ⟨x, hx, heX⟩ := exists_fan_eq_max hA
    obtain ⟨y, hy, heY⟩ := exists_fan_eq_max hB
    have hxy : Sum.elim x y ∈ coordinateProduct A B := mem_coordinateProduct.mpr ⟨x, hx, y, hy, rfl⟩
    have h := card_fan_le_maxFan hxy
    rwa [fan_coordinateProduct, coordinateProduct_card, heX, heY] at h

end
end Erdos539Geometry
