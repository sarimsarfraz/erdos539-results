/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13LineCoordinates
import Erdos539.CoordinatePadding
import Erdos539.FourLeafBox

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

def pg13BranchOffset (T : ℕ) (l : Fin 13) (j : Fin 13) : ℤ :=
  if j ∈ pg13LineSet l then fourLeafShift T else fourLeafCeiling T

def pg13BranchEmbed (T : ℕ) (l : Fin 13) (x : Fin 4 → ℤ) : Fin 13 → ℤ :=
  coordinatePad (pg13LineEmbedding l) x + pg13BranchOffset T l

def pg13Branch (T : ℕ) (l : Fin 13) : Finset (Fin 13 → ℤ) :=
  (fourLeafBranch T).image (pg13BranchEmbed T l)

def pg13Union (T : ℕ) : Finset (Fin 13 → ℤ) :=
  Finset.univ.biUnion (pg13Branch T)

@[simp] theorem pg13BranchEmbed_at (T : ℕ) (l : Fin 13) (x : Fin 4 → ℤ) (i : Fin 4) :
    pg13BranchEmbed T l x (pg13LineEmbedding l i) = x i + fourLeafShift T := by
  simp [pg13BranchEmbed, pg13BranchOffset, pg13LineEmbedding_mem]

theorem pg13BranchEmbed_off (T : ℕ) (l : Fin 13) (x : Fin 4 → ℤ) (j : Fin 13)
    (hj : j ∉ pg13LineSet l) : pg13BranchEmbed T l x j = fourLeafCeiling T := by
  have hh : ¬ ∃ i, pg13LineEmbedding l i = j := by rwa [← pg13_mem_line_iff]
  simp [pg13BranchEmbed, pg13BranchOffset, hj, coordinatePad_off _ _ _ hh]

theorem pg13BranchEmbed_injective (T : ℕ) (l : Fin 13) :
    Function.Injective (pg13BranchEmbed T l) := by
  intro x y he
  funext i
  have h := congrFun he (pg13LineEmbedding l i)
  simpa only [pg13BranchEmbed_at, add_left_inj] using h

theorem pg13Branch_card (T : ℕ) (l : Fin 13) : (pg13Branch T l).card = T ^ 7 := by
  rw [pg13Branch, Finset.card_image_of_injective _ (pg13BranchEmbed_injective T l), fourLeafBranch_card]

theorem pg13Branch_coordinate_bounds {T : ℕ} (hT : 0 < T) (l : Fin 13)
    {x : Fin 13 → ℤ} (hx : x ∈ pg13Branch T l) (j : Fin 13) :
    (j ∈ pg13LineSet l → 0 < x j ∧ x j < fourLeafCeiling T) ∧
      (j ∉ pg13LineSet l → x j = fourLeafCeiling T) := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  constructor
  · intro hj
    obtain ⟨i, rfl⟩ := (pg13_mem_line_iff l j).mp hj
    rw [pg13BranchEmbed_at]
    exact fourLeafBranch_shift_bounds hT ha i
  · exact pg13BranchEmbed_off T l a j

theorem pg13Branch_identifies_line {T : ℕ} (hT : 0 < T) (l : Fin 13)
    {x : Fin 13 → ℤ} (hx : x ∈ pg13Branch T l) (j : Fin 13) :
    x j < fourLeafCeiling T ↔ j ∈ pg13LineSet l := by
  have h := pg13Branch_coordinate_bounds hT l hx j
  constructor
  · intro hj
    by_contra hn
    exact (ne_of_lt hj) (h.2 hn)
  · exact fun hj ↦ (h.1 hj).2

theorem pg13Branches_disjoint {T : ℕ} (hT : 0 < T) {l m : Fin 13} (hlm : l ≠ m) :
    Disjoint (pg13Branch T l) (pg13Branch T m) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have he : pg13LineSet l = pg13LineSet m := by
    ext j
    exact (pg13Branch_identifies_line hT l hx j).symm.trans (pg13Branch_identifies_line hT m hy j)
  exact hlm (pg13_line_coordinates_certificate.2.2.2 l m he)

/-- Cardinality of the actual thirteen-branch integer union. -/
theorem pg13Union_card {T : ℕ} (hT : 0 < T) : (pg13Union T).card = 13 * T ^ 7 := by
  rw [pg13Union, Finset.card_biUnion]
  · simp [pg13Branch_card]
  · intro l _ m _ hlm
    exact pg13Branches_disjoint hT hlm

end
end Erdos539Geometry
