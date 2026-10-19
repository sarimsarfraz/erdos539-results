/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LatticeCongruence
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M]

/-- Elements of a lattice group supported on a prescribed coordinate block. -/
def latticeSupported (e : M →ₗ[ℤ] (ι → ℝ)) (I : Finset ι) : Submodule ℤ M where
  carrier := {x | ∀ i, i ∉ I → e x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    change e (x + y) i = 0
    rw [map_add]
    change e x i + e y i = 0
    rw [hx i hi, hy i hi, zero_add]
  smul_mem' := by
    intro n x hx i hi
    change e (n • x) i = 0
    rw [map_smul]
    change n • e x i = 0
    rw [hx i hi, smul_zero]

/-- Addition of the two supported subgroups inside the parent group. -/
def latticeSupportedSum (e : M →ₗ[ℤ] (ι → ℝ)) (I J : Finset ι) :
    latticeSupported e I × latticeSupported e J →ₗ[ℤ] M where
  toFun := fun z ↦ z.1.val + z.2.val
  map_add' := by intros; simp; abel
  map_smul' := by intros; simp

theorem latticeSupportedSum_injective (e : M →ₗ[ℤ] (ι → ℝ)) (I J : Finset ι)
    (he : Function.Injective e) (hIJ : Disjoint I J) : Function.Injective (latticeSupportedSum e I J) := by
  intro x y h
  have hx : x.1 = y.1 := by
    apply Subtype.ext
    apply he
    funext i
    by_cases hi : i ∈ I
    · have hj : i ∉ J := fun hj ↦ Finset.disjoint_left.mp hIJ hi hj
      have hxi : e x.2.val i = 0 := x.2.property i hj
      have hyi : e y.2.val i = 0 := y.2.property i hj
      have heq := congrArg (fun z : M ↦ e z i) h
      simp only [latticeSupportedSum, LinearMap.coe_mk, AddHom.coe_mk, map_add, Pi.add_apply] at heq
      simpa only [hxi, hyi, add_zero] using heq
    · exact (x.1.property i hi).trans (y.1.property i hi).symm
  apply Prod.ext hx
  apply Subtype.ext
  change x.1.val + x.2.val = y.1.val + y.2.val at h
  rw [hx] at h
  exact add_left_cancel h

/-- The ranks of subgroups on disjoint blocks add to at most the parent rank. -/
theorem latticeSupported_finrank_add_le (e : M →ₗ[ℤ] (ι → ℝ))
    [Module.Free ℤ M] [Module.Finite ℤ M] (I J : Finset ι) (he : Function.Injective e) (hIJ : Disjoint I J) :
    Module.finrank ℤ (latticeSupported e I) + Module.finrank ℤ (latticeSupported e J) ≤
      Module.finrank ℤ M := by
  have h := (latticeSupportedSum e I J).finrank_le_finrank_of_injective
    (latticeSupportedSum_injective e I J he hIJ)
  rwa [Module.finrank_prod] at h

end
end Erdos539Geometry
