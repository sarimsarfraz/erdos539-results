/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Branches
import Erdos539.FourLeafFans
import Erdos539.FourLeafProjectionCard
import Erdos539.IntegerFans

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem integerToReal_coordinatePad {ι κ : Type} (e : ι ↪ κ) (x : ι → ℤ) :
    integerToReal (coordinatePad e x) = coordinatePad e (integerToReal x) := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [integerToReal]
  · simp [integerToReal, coordinatePad_off e _ j hj]

theorem pg13Branch_real (T : ℕ) (l : Fin 13) :
    integerRealSet (pg13Branch T l) =
      translateRealSet ((integerRealSet (fourLeafBranch T)).image (coordinatePad (pg13LineEmbedding l)))
        (integerToReal (pg13BranchOffset T l)) := by
  simp only [integerRealSet, pg13Branch, translateRealSet, Finset.image_image]
  congr 1
  funext x
  change integerToReal (coordinatePad (pg13LineEmbedding l) x + pg13BranchOffset T l) = _
  have he : integerToReal (coordinatePad (pg13LineEmbedding l) x + pg13BranchOffset T l) =
      integerToReal (coordinatePad (pg13LineEmbedding l) x) + integerToReal (pg13BranchOffset T l) := by
    funext j
    simp [integerToReal]
  rw [he, integerToReal_coordinatePad]
  rfl

theorem pg13Branch_maxFan (T : ℕ) (l : Fin 13) :
    maxFan (integerRealSet (pg13Branch T l)) = maxFan (integerRealSet (fourLeafBranch T)) := by
  rw [pg13Branch_real, maxFan_translateRealSet]
  exact maxFan_coordinatePad (pg13LineEmbedding l) (integerRealSet (fourLeafBranch T))

theorem pg13Branch_coordinate_card {T : ℕ} (hT : 0 < T) (l : Fin 13) {j : Fin 13}
    (hj : j ∈ pg13LineSet l) : ((pg13Branch T l).image (fun x ↦ x j)).card = T ^ 3 := by
  obtain ⟨i, rfl⟩ := (pg13_mem_line_iff l j).mp hj
  have he : (pg13Branch T l).image (fun x ↦ x (pg13LineEmbedding l i)) =
      ((fourLeafBranch T).image (fun x ↦ x i)).image (fun t ↦ t + fourLeafShift T) := by
    simp only [pg13Branch, Finset.image_image]
    congr 1
    funext x
    exact pg13BranchEmbed_at T l x i
  rw [he, Finset.card_image_of_injective _ (add_left_injective _), fourLeafBranch_coordinate_card hT]

end
end Erdos539Geometry
