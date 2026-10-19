/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LatticeCongruence
import Mathlib.Data.Finset.Preimage

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Midpoint closure relative to the ambient additive group. Only midpoints
that actually lie in that group are required. -/
def GroupMidpointClosed (F : Finset M) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, ∀ z : M, x + y = (2 : ℤ) • z → z ∈ F

def GroupSymmetric (F : Finset M) : Prop := ∀ x ∈ F, -x ∈ F

/-- Midpoint closure passes to an injectively parametrized subgroup. -/
theorem GroupMidpointClosed.preimage {F : Finset M} (hF : GroupMidpointClosed F)
    (e : N →ₗ[ℤ] M) (he : Function.Injective e) :
    GroupMidpointClosed (F.preimage e he.injOn) := by
  intro x hx y hy z hz
  apply Finset.mem_preimage.mpr
  apply hF (e x) (Finset.mem_preimage.mp hx) (e y) (Finset.mem_preimage.mp hy) (e z)
  rw [← map_add, ← map_smul, hz]

theorem GroupSymmetric.preimage {F : Finset M} (hF : GroupSymmetric F)
    (e : N →ₗ[ℤ] M) (he : Function.Injective e) :
    GroupSymmetric (F.preimage e he.injOn) := by
  intro x hx
  apply Finset.mem_preimage.mpr
  rw [map_neg]
  exact hF (e x) (Finset.mem_preimage.mp hx)

def groupTranslate (F : Finset M) (a : M) : Finset M := F.image (fun x ↦ x - a)

@[simp] theorem mem_groupTranslate {F : Finset M} {a z : M} :
    z ∈ groupTranslate F a ↔ ∃ x ∈ F, x - a = z := Finset.mem_image

theorem groupTranslate_card (F : Finset M) (a : M) : (groupTranslate F a).card = F.card :=
  Finset.card_image_of_injective _ (fun _ _ h ↦ sub_left_injective h)

theorem GroupMidpointClosed.translate {F : Finset M} (hF : GroupMidpointClosed F) (a : M) :
    GroupMidpointClosed (groupTranslate F a) := by
  intro x hx y hy z hz
  obtain ⟨x', hx', rfl⟩ := mem_groupTranslate.mp hx
  obtain ⟨y', hy', rfl⟩ := mem_groupTranslate.mp hy
  have he : x' + y' = (2 : ℤ) • (z + a) := by
    calc
      _ = (x' - a + (y' - a)) + (a + a) := by abel
      _ = (2 : ℤ) • z + (a + a) := by rw [hz]
      _ = _ := by simp only [smul_add, two_zsmul]
  exact mem_groupTranslate.mpr ⟨z + a, hF x' hx' y' hy' (z + a) he, add_sub_cancel_right z a⟩

/-- The part of F symmetric around a given center. -/
def symmetricCore (F : Finset M) (a : M) : Finset M :=
  F.filter (fun x ↦ (2 : ℤ) • a - x ∈ F)

@[simp] theorem mem_symmetricCore {F : Finset M} {a x : M} :
    x ∈ symmetricCore F a ↔ x ∈ F ∧ (2 : ℤ) • a - x ∈ F := Finset.mem_filter

theorem GroupMidpointClosed.symmetricCore {F : Finset M} (hF : GroupMidpointClosed F) (a : M) :
    GroupMidpointClosed (symmetricCore F a) := by
  intro x hx y hy z hz
  obtain ⟨hx, hx'⟩ := mem_symmetricCore.mp hx
  obtain ⟨hy, hy'⟩ := mem_symmetricCore.mp hy
  apply mem_symmetricCore.mpr
  refine ⟨hF x hx y hy z hz, hF _ hx' _ hy' _ ?_⟩
  calc
    _ = (2 : ℤ) • a + (2 : ℤ) • a - (x + y) := by abel
    _ = (2 : ℤ) • a + (2 : ℤ) • a - (2 : ℤ) • z := by rw [hz]
    _ = _ := by simp only [two_zsmul]; abel

theorem centered_symmetricCore_symmetric (F : Finset M) (a : M) :
    GroupSymmetric (groupTranslate (symmetricCore F a) a) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_groupTranslate.mp hx
  obtain ⟨hy, hy'⟩ := mem_symmetricCore.mp hy
  apply mem_groupTranslate.mpr
  refine ⟨(2 : ℤ) • a - y, mem_symmetricCore.mpr ⟨hy', ?_⟩, ?_⟩
  · simpa only [sub_sub_cancel] using hy
  · simp only [two_zsmul]
    abel

theorem zero_mem_centered_symmetricCore {F : Finset M} {a : M} (ha : a ∈ F) :
    0 ∈ groupTranslate (symmetricCore F a) a := by
  apply mem_groupTranslate.mpr
  refine ⟨a, mem_symmetricCore.mpr ⟨ha, ?_⟩, sub_self a⟩
  simpa only [two_zsmul, add_sub_cancel_right] using ha

end
end Erdos539Geometry
