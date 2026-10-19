/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13AllCuts
import Init.Data.BitVec.Lemmas

namespace Erdos539Geometry

def pg13MaskSet (m : Fin 8192) : Finset (Fin 13) :=
  Finset.univ.filter (fun i ↦ m.val.testBit i.val)

def pg13SetMask (I : Finset (Fin 13)) : Fin 8192 :=
  let b := BitVec.ofBoolListLE (List.ofFn (fun i : Fin 13 ↦ decide (i ∈ I)))
  ⟨b.toNat, by have h := b.isLt; simpa only [List.length_ofFn] using h⟩

theorem pg13SetMask_bit (I : Finset (Fin 13)) (i : Fin 13) :
    (pg13SetMask I).val.testBit i.val = decide (i ∈ I) := by
  change (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 13 ↦ decide (j ∈ I)))).getLsbD i.val = _
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> simp [List.getD]

/-- Every literal coordinate subset occurs among the checked masks. -/
theorem pg13MaskSet_setMask (I : Finset (Fin 13)) : pg13MaskSet (pg13SetMask I) = I := by
  ext i
  simp [pg13MaskSet, pg13SetMask_bit]

theorem pg13MaskSet_surjective : Function.Surjective pg13MaskSet :=
  fun I ↦ ⟨pg13SetMask I, pg13MaskSet_setMask I⟩

end Erdos539Geometry
