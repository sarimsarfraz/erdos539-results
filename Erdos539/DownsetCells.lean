/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProfileSumsets
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]

def activeCoordinates (a : ι → ℕ) : Finset ι := Finset.univ.filter (fun i ↦ 0 < a i)

def NatDownset (A : Finset (ι → ℕ)) : Prop :=
  ∀ ⦃a b⦄, b ∈ A → a ≤ b → a ∈ A

/-- Doubled cells have disjoint rounded-up halves, including zero coordinates. -/
def doubledCell (a : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun i ↦ {2 * a i, 2 * a i - 1})

theorem mem_doubledCell {a z : ι → ℕ} :
    z ∈ doubledCell a ↔ ∀ i, z i = 2 * a i ∨ z i = 2 * a i - 1 := by
  simp [doubledCell, Fintype.mem_piFinset]

theorem doubledCell_card (a : ι → ℕ) :
    (doubledCell a).card = 2 ^ (activeCoordinates a).card := by
  rw [doubledCell, Fintype.card_piFinset]
  have he : ∀ i, ({2 * a i, 2 * a i - 1} : Finset ℕ).card = if 0 < a i then 2 else 1 := by
    intro i
    by_cases h : 0 < a i
    · simp [h, show 2 * a i ≠ 2 * a i - 1 by omega]
    · simp [show a i = 0 by omega]
  simp_rw [he]
  rw [Finset.prod_ite]
  simp [activeCoordinates]

theorem doubledCell_disjoint {a b : ι → ℕ} (hab : a ≠ b) :
    Disjoint (doubledCell a) (doubledCell b) := by
  apply Finset.disjoint_left.mpr
  intro z hza hzb
  apply hab
  funext i
  have ha := mem_doubledCell.mp hza i
  have hb := mem_doubledCell.mp hzb i
  omega

theorem doubledCell_subset_add {A : Finset (ι → ℕ)} (hA : NatDownset A)
    {a : ι → ℕ} (ha : a ∈ A) : doubledCell a ⊆ A + A := by
  intro z hz
  have hza : a ≤ z := by
    intro i
    change a i ≤ z i
    have hi := mem_doubledCell.mp hz i
    omega
  have hdiff : z - a ≤ a := by
    intro i
    have hi := mem_doubledCell.mp hz i
    change z i - a i ≤ a i
    omega
  have he : a + (z - a) = z := by
    funext i
    exact Nat.add_sub_cancel' (hza i)
  exact Finset.mem_add.mpr ⟨a, ha, z - a, hA ha hdiff, he⟩

/-- The support moment is controlled by the actual sumset cardinality. -/
theorem support_moment_le_sumset {A : Finset (ι → ℕ)} (hA : NatDownset A) :
    ∑ a ∈ A, 2 ^ (activeCoordinates a).card ≤ (A + A).card := by
  calc
    _ = ∑ a ∈ A, (doubledCell a).card := by simp_rw [doubledCell_card]
    _ = (A.biUnion doubledCell).card := (Finset.card_biUnion (fun _ _ _ _ h ↦ doubledCell_disjoint h)).symm
    _ ≤ _ := Finset.card_le_card (Finset.biUnion_subset.mpr (fun _ ha ↦ doubledCell_subset_add hA ha))

/-- Trimming expensive supports retains half the points once the support
threshold dominates twice the sum doubling. The premise has no logarithms. -/
theorem support_trim_half {A : Finset (ι → ℕ)} (hA : NatDownset A) (r : ℕ)
    (hbudget : 2 * (A + A).card ≤ 2 ^ r * A.card) :
    A.card ≤ 2 * (A.filter (fun a ↦ (activeCoordinates a).card ≤ r)).card := by
  let B := A.filter (fun a ↦ ¬(activeCoordinates a).card ≤ r)
  have hB : 2 ^ r * B.card ≤ ∑ a ∈ B, 2 ^ (activeCoordinates a).card := by
    calc
      _ = ∑ _a ∈ B, 2 ^ r := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun a ha ↦ Nat.pow_le_pow_right (by decide)
        (by have := (Finset.mem_filter.mp ha).2; omega))
  have hsum : ∑ a ∈ B, 2 ^ (activeCoordinates a).card ≤ (A + A).card := by
    exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans (support_moment_le_sumset hA)
  have hc : (A.filter (fun a ↦ (activeCoordinates a).card ≤ r)).card + B.card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have hp : 0 < 2 ^ r := Nat.pow_pos (by decide)
  have hb : 2 * B.card ≤ A.card := by
    exact Nat.le_of_mul_le_mul_left (show 2 ^ r * (2 * B.card) ≤ 2 ^ r * A.card by nlinarith) hp
  omega

end
end Erdos539Geometry
