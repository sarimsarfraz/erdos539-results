/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LatticeSupports
import Erdos539.MidpointClosure

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M]

/-- Parametrize twice the subgroup supported on a coordinate block. -/
def supportedDouble (e : M →ₗ[ℤ] (ι → ℝ)) (I : Finset ι) : latticeSupported e I →ₗ[ℤ] M :=
  (2 : ℤ) • (latticeSupported e I).subtype

theorem supportedDouble_injective (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) (I : Finset ι) :
    Function.Injective (supportedDouble e I) := by
  intro x y h
  apply Subtype.ext
  apply he
  funext i
  have hh := congrArg (fun z : M ↦ e z i) h
  change e ((2 : ℤ) • x.val) i = e ((2 : ℤ) • y.val) i at hh
  simp only [two_zsmul, map_add, Pi.add_apply] at hh
  linarith

/-- The child embedding in the smaller coordinate space represents the
actual subgroup 2 Gamma_I, while retaining Gamma_I as its abstract free group. -/
def supportedChildEmbedding (e : M →ₗ[ℤ] (ι → ℝ)) (I : Finset ι) :
    latticeSupported e I →ₗ[ℤ] (I → ℝ) where
  toFun := fun x i ↦ e (supportedDouble e I x) i
  map_add' := by
    intro x y
    funext i
    simp only [map_add, Pi.add_apply]
  map_smul' := by
    intro n x
    funext i
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem supportedChildEmbedding_injective (e : M →ₗ[ℤ] (ι → ℝ))
    (he : Function.Injective e) (I : Finset ι) : Function.Injective (supportedChildEmbedding e I) := by
  intro x y h
  apply Subtype.ext
  apply he
  funext i
  by_cases hi : i ∈ I
  · have hh := congrFun h ⟨i, hi⟩
    change e ((2 : ℤ) • x.val) i = e ((2 : ℤ) • y.val) i at hh
    simp only [two_zsmul, map_add, Pi.add_apply] at hh
    linarith
  · exact (x.property i hi).trans (y.property i hi).symm

/-- All parent points belonging to twice the supported subgroup, in child coordinates. -/
def midpointDescendant (F : Finset M) (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) (I : Finset ι) :
    Finset (latticeSupported e I) := F.preimage (supportedDouble e I) (supportedDouble_injective e he I).injOn

@[simp] theorem mem_midpointDescendant {F : Finset M} {e : M →ₗ[ℤ] (ι → ℝ)}
    {he : Function.Injective e} {I : Finset ι} {x : latticeSupported e I} :
    x ∈ midpointDescendant F e he I ↔ (2 : ℤ) • x.val ∈ F := Finset.mem_preimage

theorem GroupMidpointClosed.descendant {F : Finset M} (hF : GroupMidpointClosed F)
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) (I : Finset ι) :
    GroupMidpointClosed (midpointDescendant F e he I) :=
  hF.preimage (supportedDouble e I) (supportedDouble_injective e he I)

theorem GroupSymmetric.descendant {F : Finset M} (hF : GroupSymmetric F)
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) (I : Finset ι) :
    GroupSymmetric (midpointDescendant F e he I) :=
  hF.preimage (supportedDouble e I) (supportedDouble_injective e he I)

theorem zero_mem_midpointDescendant {F : Finset M} (hF : 0 ∈ F)
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) (I : Finset ι) :
    0 ∈ midpointDescendant F e he I := by
  apply Finset.mem_preimage.mpr
  simpa only [map_zero] using hF

/-- Halves of two supported child points add to a parent point. -/
theorem midpointDescendant_add_mem {F : Finset M} (hF : GroupMidpointClosed F)
    {e : M →ₗ[ℤ] (ι → ℝ)} {he : Function.Injective e} {I J : Finset ι}
    {x : latticeSupported e I} {y : latticeSupported e J}
    (hx : x ∈ midpointDescendant F e he I) (hy : y ∈ midpointDescendant F e he J) :
    x.val + y.val ∈ F := by
  apply hF _ (mem_midpointDescendant.mp hx) _ (mem_midpointDescendant.mp hy) _
  exact (smul_add (2 : ℤ) x.val y.val).symm

end
end Erdos539Geometry
