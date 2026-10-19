/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProductLaws
import Erdos539.FiniteDataProcessing
import Erdos539.StationaryLawPush

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

def productSupportEquiv {G H : Type*} (S : Finset G) (T : Finset H) : (S × T) ≃ (S ×ˢ T) where
  toFun z := ⟨(z.1.val, z.2.val), Finset.mem_product.mpr ⟨z.1.property, z.2.property⟩⟩
  invFun z := (⟨z.val.1, (Finset.mem_product.mp z.property).1⟩, ⟨z.val.2, (Finset.mem_product.mp z.property).2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

def productSupportFirst {G H : Type*} (S : Finset G) (T : Finset H) (z : S ×ˢ T) : S :=
  ((productSupportEquiv S T).symm z).1

def productSupportSecond {G H : Type*} (S : Finset G) (T : Finset H) (z : S ×ˢ T) : T :=
  ((productSupportEquiv S T).symm z).2

/-- Independent endpoint laws on the literal Cartesian product support. -/
def productSupportLaw {G H : Type*} (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ) (z : S ×ˢ T) : ℝ :=
  ν (productSupportFirst S T z) * η (productSupportSecond S T z)

theorem finitePush_productSupportEquiv {G H : Type*} (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ) :
    finitePush (finiteProductWeight ν η) (productSupportEquiv S T) = productSupportLaw S T ν η := by
  funext z
  rw [finitePush_equiv_apply]
  rfl

theorem productSupportLaw_nonneg {G H : Type*} (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hη : ∀ y, 0 ≤ η y) (z : S ×ˢ T) : 0 ≤ productSupportLaw S T ν η z :=
  mul_nonneg (hν _) (hη _)

theorem productSupportLaw_sum {G H : Type*} (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hνs : ∑ x, ν x = 1) (hηs : ∑ y, η y = 1) : ∑ z, productSupportLaw S T ν η z = 1 := by
  rw [← finitePush_productSupportEquiv, finitePush_sum, finiteProductWeight_sum, hνs, hηs, one_mul]

theorem productSupportLaw_first {G H : Type*} (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hηs : ∑ y, η y = 1) : finitePush (productSupportLaw S T ν η) (productSupportFirst S T) = ν := by
  rw [← finitePush_productSupportEquiv, finitePush_comp]
  change finitePush (finiteProductWeight ν η) Prod.fst = ν
  funext x
  rw [finitePush_fst]
  simp only [finiteProductWeight, ← Finset.mul_sum, hηs, mul_one]

theorem productSupportLaw_second {G H : Type*} (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hνs : ∑ x, ν x = 1) : finitePush (productSupportLaw S T ν η) (productSupportSecond S T) = η := by
  rw [← finitePush_productSupportEquiv, finitePush_comp]
  change finitePush (finiteProductWeight ν η) Prod.snd = η
  funext y
  rw [finitePush_snd]
  simp only [finiteProductWeight, ← Finset.sum_mul, hνs, one_mul]

theorem productSupportLaw_entropy {G H : Type*} (S : Finset G) (T : Finset H) (ν : S → ℝ) (η : T → ℝ)
    (hνs : ∑ x, ν x = 1) (hηs : ∑ y, η y = 1) :
    finiteEntropy (productSupportLaw S T ν η) = finiteEntropy ν + finiteEntropy η := by
  rw [← finitePush_productSupportEquiv,
    finiteEntropy_push_eq_of_support_injective _ (productSupportEquiv S T)
      (fun a b _ _ he ↦ (productSupportEquiv S T).injective he),
    finiteProductWeight_entropy ν η hνs hηs]

/-- Regroup the endpoints of two actual quadruples into one quadruple
on the Cartesian product support. -/
def productQuadrupleEquiv {G H : Type*} (S : Finset G) (T : Finset H) :
    (((S × S) × (S × S)) × ((T × T) × (T × T))) ≃
      (((S ×ˢ T) × (S ×ˢ T)) × ((S ×ˢ T) × (S ×ˢ T))) where
  toFun z :=
    ((productSupportEquiv S T (z.1.1.1, z.2.1.1), productSupportEquiv S T (z.1.1.2, z.2.1.2)),
      (productSupportEquiv S T (z.1.2.1, z.2.2.1), productSupportEquiv S T (z.1.2.2, z.2.2.2)))
  invFun z :=
    (((productSupportFirst S T z.1.1, productSupportFirst S T z.1.2),
      (productSupportFirst S T z.2.1, productSupportFirst S T z.2.2)),
      ((productSupportSecond S T z.1.1, productSupportSecond S T z.1.2),
      (productSupportSecond S T z.2.1, productSupportSecond S T z.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

end
end Erdos539Geometry
