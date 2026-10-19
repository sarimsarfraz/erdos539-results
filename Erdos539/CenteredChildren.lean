/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CenteredSignClasses
import Erdos539.MidpointProduct

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M]

/-- The projection on a full block preserves every point of a faithful model. -/
theorem full_embedded_projection_card (e : M →ₗ[ℤ] (ι → ℝ))
    (he : Function.Injective e) (I : Finset ι) (hI : ∀ i, i ∈ I) (E : Finset M) :
    (E.image (fun x ↦ project I (e x))).card = E.card := by
  classical
  apply Finset.card_image_of_injective
  intro x y h
  apply he
  funext i
  exact congrFun h ⟨i, hI i⟩

/-- A complementary coordinate fiber is an affine coset of the supported subgroup. -/
theorem centered_child_card [Module.Free ℤ M] [Module.Finite ℤ M]
    {F E : Finset M} (hF : GroupMidpointClosed F) (hsym : GroupSymmetric F)
    (hEF : E ⊆ F) (hE : E.Nonempty) (e : M →ₗ[ℤ] (ι → ℝ))
    (he : Function.Injective e) (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {q : ℕ} (hQ : (E.image (fun x ↦ project J (e x))).card ≤ q) :
    E.card ≤ q * 4 ^ Module.finrank ℤ (latticeSupported e I) *
      (midpointDescendant F e he I).card := by
  classical
  let f : M → (J → ℝ) := fun x ↦ project J (e x)
  obtain ⟨a, ha, hlarge⟩ := exists_large_fiber E hE f
  let H := fiber E f (f a)
  have hHF : H ⊆ F := fun _ hx ↦ hEF (mem_fiber.mp hx).1
  have hH : H.Nonempty := ⟨a, mem_fiber.mpr ⟨ha, rfl⟩⟩
  have hcoset : ∀ x ∈ H, x - a ∈ latticeSupported e I := by
    intro x hx i hi
    have hj := (hcover i).resolve_left hi
    have hh := congrFun (mem_fiber.mp hx).2 ⟨i, hj⟩
    change e x i = e a i at hh
    simp only [map_sub, Pi.sub_apply, hh, sub_self]
  have hchild := midpointDescendant_card_from_coset hF hsym hHF hH e he I a hcoset
  calc
    E.card ≤ (E.image f).card * H.card := hlarge
    _ ≤ q * H.card := Nat.mul_le_mul_right _ hQ
    _ ≤ q * (4 ^ Module.finrank ℤ (latticeSupported e I) * (midpointDescendant F e he I).card) :=
      Nat.mul_le_mul_left _ hchild
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- Each actual descendant has size at least the parent divided by the
sign-class count, the common positive-part count, and its rank loss. -/
theorem centered_child_from_sign_class [Fintype ι] [Module.Free ℤ M] [Module.Finite ℤ M]
    {F E : Finset M} (hF : GroupMidpointClosed F) (hsym : GroupSymmetric F)
    (hEF : E ⊆ F) (hE : E.Nonempty) (e : M →ₗ[ℤ] (ι → ℝ))
    (he : Function.Injective e) (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {q : ℕ} (hQ : (E.image (fun x ↦ project J (e x))).card ≤ q)
    (hlarge : F.card ≤ 2 ^ Fintype.card ι * E.card) :
    F.card ≤ 2 ^ Fintype.card ι * q * 4 ^ Module.finrank ℤ (latticeSupported e I) *
      (midpointDescendant F e he I).card := by
  have h := centered_child_card hF hsym hEF hE e he I J hcover hQ
  calc
    F.card ≤ 2 ^ Fintype.card ι * E.card := hlarge
    _ ≤ 2 ^ Fintype.card ι * (q * 4 ^ Module.finrank ℤ (latticeSupported e I) *
        (midpointDescendant F e he I).card) := Nat.mul_le_mul_left _ h
    _ = _ := by ring

end
end Erdos539Geometry
