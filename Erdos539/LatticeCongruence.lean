/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignClasses
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Data.ZMod.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {M : Type*} [AddCommGroup M]

/-- Residue coordinates in an actual integral basis. -/
def latticeColor {r : ℕ} (e : M ≃ₗ[ℤ] (Fin r → ℤ)) (m : ℕ) (x : M) : Fin r → ZMod m :=
  fun i ↦ (e x i : ZMod m)

/-- Equal residue profiles give a multiple inside the same free group. -/
theorem latticeColor_eq_divisible {r m : ℕ} (e : M ≃ₗ[ℤ] (Fin r → ℤ)) {x y : M}
    (h : latticeColor e m x = latticeColor e m y) :
    ∃ z : M, x - y = (m : ℤ) • z := by
  have hdiv (i : Fin r) : (m : ℤ) ∣ e x i - e y i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (e y i) (e x i) m).mp (congrFun h i).symm
  choose w hw using hdiv
  refine ⟨e.symm w, ?_⟩
  apply e.injective
  rw [map_sub, map_smul, e.apply_symm_apply]
  funext i
  exact hw i

/-- Pigeonholing modulo m retains a fraction m^(-r) in a rank-r free group. -/
theorem exists_large_lattice_congruence_class {r m : ℕ} [NeZero m]
    (e : M ≃ₗ[ℤ] (Fin r → ℤ)) {F : Finset M} (hF : F.Nonempty) :
    ∃ S ⊆ F, S.Nonempty ∧ F.card ≤ m ^ r * S.card ∧
      ∀ x ∈ S, ∀ y ∈ S, ∃ z : M, x - y = (m : ℤ) • z := by
  classical
  obtain ⟨a, ha, hsize⟩ := exists_large_fiber F hF (latticeColor e m)
  let S := fiber F (latticeColor e m) (latticeColor e m a)
  have hcolors : (F.image (latticeColor e m)).card ≤ m ^ r := by
    have h := Finset.card_le_univ (F.image (latticeColor e m))
    simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using h
  refine ⟨S, (fun _ hx ↦ (mem_fiber.mp hx).1), ⟨a, mem_fiber.mpr ⟨ha, rfl⟩⟩,
    hsize.trans (Nat.mul_le_mul_right _ hcolors), ?_⟩
  intro x hx y hy
  exact latticeColor_eq_divisible e ((mem_fiber.mp hx).2.trans (mem_fiber.mp hy).2.symm)

/-- Basis-independent form for every finite free abelian group. -/
theorem exists_large_free_congruence_class [Module.Free ℤ M] [Module.Finite ℤ M]
    {m : ℕ} [NeZero m] {F : Finset M} (hF : F.Nonempty) :
    ∃ S ⊆ F, S.Nonempty ∧ F.card ≤ m ^ Module.finrank ℤ M * S.card ∧
      ∀ x ∈ S, ∀ y ∈ S, ∃ z : M, x - y = (m : ℤ) • z :=
  exists_large_lattice_congruence_class (Module.finBasis ℤ M).equivFun hF

end
end Erdos539Geometry
