/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerGeometry

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

def integerProduct (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) : Finset (ι ⊕ κ → ℤ) :=
  (F ×ˢ G).image (fun p ↦ Sum.elim p.1 p.2)

@[simp] theorem mem_integerProduct {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)} {z : ι ⊕ κ → ℤ} :
    z ∈ integerProduct F G ↔ ∃ x ∈ F, ∃ y ∈ G, Sum.elim x y = z := by
  simp only [integerProduct, Finset.mem_image, Prod.exists, Finset.mem_product]
  aesop

theorem integerProduct_card (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) :
    (integerProduct F G).card = F.card * G.card := by
  rw [integerProduct, Finset.card_image_of_injective]
  · exact Finset.card_product _ _
  · intro p q hpq
    apply Prod.ext
    · funext i
      exact congrFun hpq (Sum.inl i)
    · funext j
      exact congrFun hpq (Sum.inr j)

theorem integerProduct_positiveDifferences (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) :
    integerPositiveDifferences (integerProduct F G) =
      integerProduct (integerPositiveDifferences F) (integerPositiveDifferences G) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerPositiveDifferences.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerProduct.mp hx
    obtain ⟨u', hu', v', hv', rfl⟩ := mem_integerProduct.mp hy
    refine mem_integerProduct.mpr ⟨intPdiff u u', mem_integerPositiveDifferences.mpr ⟨u, hu, u', hu', rfl⟩,
      intPdiff v v', mem_integerPositiveDifferences.mpr ⟨v, hv, v', hv', rfl⟩, ?_⟩
    funext i
    cases i <;> rfl
  · intro hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerProduct.mp hz
    obtain ⟨x, hx, x', hx', rfl⟩ := mem_integerPositiveDifferences.mp hu
    obtain ⟨y, hy, y', hy', rfl⟩ := mem_integerPositiveDifferences.mp hv
    refine mem_integerPositiveDifferences.mpr
      ⟨Sum.elim x y, mem_integerProduct.mpr ⟨x, hx, y, hy, rfl⟩,
      Sum.elim x' y', mem_integerProduct.mpr ⟨x', hx', y', hy', rfl⟩, ?_⟩
    funext i
    cases i <;> rfl

theorem integerProduct_differences (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) :
    integerDifferences (integerProduct F G) =
      integerProduct (integerDifferences F) (integerDifferences G) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerDifferences.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerProduct.mp hx
    obtain ⟨u', hu', v', hv', rfl⟩ := mem_integerProduct.mp hy
    refine mem_integerProduct.mpr ⟨u - u', mem_integerDifferences.mpr ⟨u, hu, u', hu', rfl⟩,
      v - v', mem_integerDifferences.mpr ⟨v, hv, v', hv', rfl⟩, ?_⟩
    funext i
    cases i <;> rfl
  · intro hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_integerProduct.mp hz
    obtain ⟨x, hx, x', hx', rfl⟩ := mem_integerDifferences.mp hu
    obtain ⟨y, hy, y', hy', rfl⟩ := mem_integerDifferences.mp hv
    refine mem_integerDifferences.mpr
      ⟨Sum.elim x y, mem_integerProduct.mpr ⟨x, hx, y, hy, rfl⟩,
      Sum.elim x' y', mem_integerProduct.mpr ⟨x', hx', y', hy', rfl⟩, ?_⟩
    funext i
    cases i <;> rfl

end
end Erdos539Geometry
