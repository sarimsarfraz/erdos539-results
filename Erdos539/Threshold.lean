/-
Copyright 2026 The Formal Conjectures Authors, Kenta Kitamura, Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0

The two definitions in namespace Erdos539 match Formal Conjectures 539.lean.
The minimum-attainment and positive-subset arguments are adapted from Kitamura,
Erdos539Asymptotic.lean, revision recorded in vendor-sources/kitamura-sqrt/SOURCE.json.
-/
import Erdos539.Factorization
import Mathlib.Data.Nat.Lattice

namespace Erdos539
open scoped Finset

def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, #A = n →
  m ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b)

noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

open Erdos539Geometry

theorem isCofactorLowerBound_iff (n m : ℕ) :
    IsCofactorLowerBound n m ↔
      ∀ A : Finset ℕ, A.card = n → m ≤ (cofactors A).card := Iff.rfl

theorem lowerBounds_bddAbove (n : ℕ) :
    BddAbove {m | IsCofactorLowerBound n m} := by
  refine ⟨n * n, ?_⟩
  intro m hm
  calc
    m ≤ (cofactors (Finset.range n)).card := hm _ (Finset.card_range n)
    _ ≤ (Finset.range n ×ˢ Finset.range n).card := Finset.card_image_le
    _ = n * n := by simp

theorem cofactorThreshold_isLowerBound (n : ℕ) :
    IsCofactorLowerBound n (cofactorThreshold n) := by
  have hne : ({m | IsCofactorLowerBound n m} : Set ℕ).Nonempty :=
    ⟨0, fun _ _ ↦ Nat.zero_le _⟩
  exact Nat.sSup_mem hne (lowerBounds_bddAbove n)

theorem le_cofactorThreshold {n m : ℕ} (h : IsCofactorLowerBound n m) :
    m ≤ cofactorThreshold n := le_csSup (lowerBounds_bddAbove n) h

theorem cofactorThreshold_le {A : Finset ℕ} {n : ℕ} (hA : A.card = n) :
    cofactorThreshold n ≤ (cofactors A).card := cofactorThreshold_isLowerBound n A hA

theorem cofactorThreshold_attained (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ (cofactors A).card = cofactorThreshold n := by
  classical
  have hex : ∃ m : ℕ, ∃ A : Finset ℕ, A.card = n ∧ (cofactors A).card = m :=
    ⟨_, Finset.range n, Finset.card_range n, rfl⟩
  obtain ⟨A, hA, hq⟩ := Nat.find_spec hex
  have hmin : IsCofactorLowerBound n (Nat.find hex) := by
    intro B hB
    exact Nat.find_min' hex ⟨B, hB, rfl⟩
  have hlo := le_cofactorThreshold hmin
  have hhi := cofactorThreshold_le hA
  exact ⟨A, hA, by omega⟩

theorem cofactors_mono {A B : Finset ℕ} (h : A ⊆ B) :
    cofactors A ⊆ cofactors B := by
  exact Finset.image_subset_image (Finset.product_subset_product h h)

theorem positive_subset_pred {A : Finset ℕ} (hA : A.Nonempty) :
    ∃ B : Finset ℕ, B ⊆ A ∧ B.card = A.card - 1 ∧ ∀ b ∈ B, 0 < b := by
  classical
  by_cases hz : 0 ∈ A
  · refine ⟨A.erase 0, Finset.erase_subset _ _, Finset.card_erase_of_mem hz, ?_⟩
    intro b hb
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hb).1
  · obtain ⟨a, ha⟩ := hA
    refine ⟨A.erase a, Finset.erase_subset _ _, Finset.card_erase_of_mem ha, ?_⟩
    intro b hb
    exact Nat.pos_of_ne_zero fun hb0 ↦ hz (hb0 ▸ (Finset.mem_erase.mp hb).2)

/-- The precise finite bridge for a lower bound proved only for positive sets. -/
theorem cofactorThreshold_succ_ge_of_positive {n m : ℕ}
    (h : ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 0 < a) →
      m ≤ (cofactors A).card) :
    m ≤ cofactorThreshold (n + 1) := by
  apply le_cofactorThreshold
  intro A hA
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B, hBA, hB, hpos⟩ := positive_subset_pred hne
  exact (h B (by omega) hpos).trans (Finset.card_le_card (cofactors_mono hBA))

end Erdos539

#print axioms Erdos539.cofactorThreshold_attained
#print axioms Erdos539.cofactorThreshold_succ_ge_of_positive
