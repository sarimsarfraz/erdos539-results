/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafEncoding

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

def fourLeafEncode (T : ℕ) (a : Fin 7 → Fin T) : Fin 4 → ℤ :=
  fourLeafLinear (10 * T) (fun j ↦ (a j : ℤ))

def fourLeafBranch (T : ℕ) : Finset (Fin 4 → ℤ) :=
  Finset.univ.image (fourLeafEncode T)

theorem fourLeafEncode_injective (T : ℕ) : Function.Injective (fourLeafEncode T) := by
  intro a b he
  have hT : (0 : ℤ) < T := by have := (a 0).isLt; omega
  have ha : ∀ j, 0 ≤ (a j : ℤ) ∧ (a j : ℤ) < 10 * T := by
    intro j; have := (a j).isLt; constructor <;> omega
  have hb : ∀ j, 0 ≤ (b j : ℤ) ∧ (b j : ℤ) < 10 * T := by
    intro j; have := (b j).isLt; constructor <;> omega
  have hh := fourLeafLinear_injective_on_box (by omega : (0 : ℤ) < 10 * T) ha hb he
  funext j
  apply Fin.ext
  exact_mod_cast congrFun hh j

theorem fourLeafBranch_card (T : ℕ) : (fourLeafBranch T).card = T ^ 7 := by
  rw [fourLeafBranch, Finset.card_image_of_injective _ (fourLeafEncode_injective T)]
  simp

end
end Erdos539Geometry
