/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedSupportCertificate
import Mathlib.Tactic.FinCases

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance reflectionAffineIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

/-- The four literal sites determining a representation in a reflected support. -/
def reflectionTestSite (w z x : ℤ) : Fin 4 → ℤ := ![x, z - x, w - x, w - z + x]

def reflectionTestInverse (w z y : ℤ) : Fin 4 → ℤ := ![y, z - y, w - y, z - w + y]

theorem reflectionTestInverse_site (w z x : ℤ) (i : Fin 4) :
    reflectionTestInverse w z (reflectionTestSite w z x i) i = x := by
  fin_cases i <;> simp [reflectionTestSite, reflectionTestInverse]
  omega

theorem reflectionTestSite_injective (w z : ℤ) (i : Fin 4) :
    Function.Injective (fun x ↦ reflectionTestSite w z x i) := by
  intro x y h
  have := congrArg (fun a ↦ reflectionTestInverse w z a i) h
  simpa only [reflectionTestInverse_site] using this

def reflectionTestSites (w z x : ℤ) : Finset ℤ := Finset.univ.image (reflectionTestSite w z x)

theorem mem_reflected_representation_iff (S : Finset ℤ) (w z x : ℤ) :
    x ∈ (reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w) ↔
      ∀ i : Fin 4, reflectionTestSite w z x i ∈ S := by
  simp only [reflectedSupport, Finset.mem_filter, reflectionTestSite, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  have he : w - (z - x) = w - z + x := by omega
  rw [he]
  tauto

/-- All failures of four-site distinctness are among the three affine coincidences. -/
theorem reflectionTest_collision {w z x : ℤ} (hzw : z ≠ w)
    (h : ¬Function.Injective (reflectionTestSite w z x)) :
    2 * x ∈ ({z, w, 2 * z - w} : Finset ℤ) := by
  by_contra hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  apply h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [reflectionTestSite] at hij ⊢ <;> omega

theorem reflectionTest_exceptional_card_le (D : Finset ℤ) {w z : ℤ} (hzw : z ≠ w) :
    (D.filter (fun x ↦ ¬Function.Injective (reflectionTestSite w z x))).card ≤ 3 := by
  let B := D.filter (fun x ↦ ¬Function.Injective (reflectionTestSite w z x))
  have hinj : Function.Injective (fun x : ℤ ↦ 2 * x) := by
    intro x y h
    change 2 * x = 2 * y at h
    omega
  have hsub : B.image (fun x ↦ 2 * x) ⊆ {z, w, 2 * z - w} := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact reflectionTest_collision hzw (Finset.mem_filter.mp hx).2
  calc
    B.card = (B.image (fun x ↦ 2 * x)).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ({z, w, 2 * z - w} : Finset ℤ).card := Finset.card_le_card hsub
    _ ≤ 3 := by
      have h₁ := Finset.card_insert_le z ({w, 2 * z - w} : Finset ℤ)
      have h₂ := Finset.card_insert_le w ({2 * z - w} : Finset ℤ)
      simp only [Finset.card_singleton] at h₂
      omega

/-- Including the test itself, at most sixteen tests can meet its four sites. -/
theorem reflectionTest_overlap_card_le (D : Finset ℤ) (w z x : ℤ) :
    (D.filter (fun y ↦ ¬Disjoint (reflectionTestSites w z x) (reflectionTestSites w z y))).card ≤ 16 := by
  let A := (Finset.univ : Finset (Fin 4 × Fin 4)).image
    (fun ij ↦ reflectionTestInverse w z (reflectionTestSite w z x ij.1) ij.2)
  have hsub : D.filter (fun y ↦ ¬Disjoint (reflectionTestSites w z x) (reflectionTestSites w z y)) ⊆ A := by
    intro y hy
    obtain ⟨a, hax, hay⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hy).2
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hax
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hay
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    dsimp only
    rw [hi, ← hj, reflectionTestInverse_site]
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by decide))

end
end Erdos539Geometry
