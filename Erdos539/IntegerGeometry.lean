/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Factorization
import Erdos539.PositiveDiff
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

def intPdiff (x y : ι → ℤ) : ι → ℤ := fun i ↦ max (x i - y i) 0

@[simp] theorem mem_integerPositiveDifferences {F : Finset (ι → ℤ)} {u : ι → ℤ} :
    u ∈ integerPositiveDifferences F ↔ ∃ x ∈ F, ∃ y ∈ F, intPdiff x y = u := by
  classical
  simp only [integerPositiveDifferences, Finset.mem_image, Prod.exists, Finset.mem_product]
  aesop

@[simp] theorem mem_integerDifferences {F : Finset (ι → ℤ)} {u : ι → ℤ} :
    u ∈ integerDifferences F ↔ ∃ x ∈ F, ∃ y ∈ F, x - y = u := by
  classical
  simp only [integerDifferences, Finset.mem_image, Prod.exists, Finset.mem_product]
  aesop

theorem integerPositiveDifferences_mono {F G : Finset (ι → ℤ)} (h : F ⊆ G) :
    integerPositiveDifferences F ⊆ integerPositiveDifferences G := by
  intro u hu
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerPositiveDifferences.mp hu
  exact mem_integerPositiveDifferences.mpr ⟨x, h hx, y, h hy, rfl⟩

theorem posDiff_integerToReal_card (F : Finset (ι → ℤ)) :
    (posDiff (F.image integerToReal)).card = (integerPositiveDifferences F).card :=
  realPositiveDifferences_integerToReal_image_card F

/-- A strict common bound on all coordinate diameters. -/
def HasCoordinateGap (F : Finset (ι → ℤ)) (M : ℤ) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| < M

/-- For a finite-dimensional finite set, a positive integral separating gap exists. -/
theorem exists_coordinate_gap [Fintype ι] (F : Finset (ι → ℤ)) :
    ∃ M : ℤ, 0 < M ∧ HasCoordinateGap F M := by
  classical
  let B : Finset ℕ := ((F ×ˢ F) ×ˢ (Finset.univ : Finset ι)).image
    (fun p ↦ (p.1.1 p.2 - p.1.2 p.2).natAbs)
  refine ⟨((B.sup id : ℕ) : ℤ) + 1, by positivity, ?_⟩
  intro x hx y hy i
  have hm : (x i - y i).natAbs ∈ B := Finset.mem_image.mpr
    ⟨((x, y), i), Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, Finset.mem_univ i⟩, rfl⟩
  have h := Finset.le_sup (f := id) hm
  have h' : ((x i - y i).natAbs : ℤ) ≤ ((B.sup id : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h'
  omega

end
end Erdos539Geometry
