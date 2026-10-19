/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteMarkovStep

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Unvisited coordinates carry none, so retaining a new coordinate is
an injective operation on the outputs accumulated by the same sweep. -/
def maskedCoordinateOutput {ι α β : Type*} (I : Finset ι)
    (q : ι → α → α → β) (a x : α) : ι → Option β :=
  fun j ↦ if j ∈ I then some (q j a x) else none

def retainedOutput {ι α β : Type*} (I : Finset ι)
    (q : ι → α → α → β) (z : α × α) : α × (ι → Option β) :=
  (z.1, maskedCoordinateOutput I q z.1 z.2)

def insertMaskedOutput {ι α β : Type*} (i : ι)
    (z : (α × (ι → Option β)) × β) : α × (ι → Option β) :=
  (z.1.1, Function.update z.1.2 i (some z.2))

theorem insertMaskedOutput_injective_on_inactive {ι α β : Type*} (i : ι)
    (u v : (α × (ι → Option β)) × β)
    (hu : u.1.2 i = none) (hv : v.1.2 i = none)
    (he : insertMaskedOutput i u = insertMaskedOutput i v) : u = v := by
  obtain ⟨⟨a, p⟩, x⟩ := u
  obtain ⟨⟨b, r⟩, y⟩ := v
  have hab : a = b := congrArg Prod.fst he
  have hfun : Function.update p i (some x) = Function.update r i (some y) := congrArg Prod.snd he
  have hxy := congrFun hfun i
  simp only [Function.update_self, Option.some.injEq] at hxy
  have hpr : p = r := by
    funext j
    by_cases hj : j = i
    · subst j
      exact hu.trans hv.symm
    · have h := congrFun hfun j
      simpa only [Function.update_of_ne hj] using h
  exact Prod.ext (Prod.ext hab hpr) hxy

theorem maskedCoordinateOutput_inactive {ι α β : Type*} (I : Finset ι)
    (q : ι → α → α → β) (a x : α) {i : ι} (hi : i ∉ I) :
    maskedCoordinateOutput I q a x i = none := by simp only [maskedCoordinateOutput, if_neg hi]

/-- Exact output identification for one update at a previously unvisited
coordinate. Old increments are preserved and the new increment uses the
old original coordinate, which has not yet changed. -/
theorem retainedOutput_insert_step {ι α β : Type*} (I : Finset ι) (i : ι)
    (q : ι → α → α → β) (a y x : α)
    (hnew : q i a x = q i y x) (hold : ∀ j ∈ I, q j a x = q j a y) :
    retainedOutput (insert i I) q (a, x) =
      insertMaskedOutput i (retainedOutput I q (a, y), q i y x) := by
  apply Prod.ext
  · rfl
  funext j
  by_cases hj : j = i
  · subst j
    simp [retainedOutput, maskedCoordinateOutput, insertMaskedOutput, hnew]
  · by_cases hI : j ∈ I
    · simp only [retainedOutput, maskedCoordinateOutput, insertMaskedOutput,
        Function.update_of_ne hj, Finset.mem_insert, hj, false_or, if_pos hI, hold j hI]
    · simp only [retainedOutput, maskedCoordinateOutput, insertMaskedOutput,
        Function.update_of_ne hj, Finset.mem_insert, hj, false_or, if_neg hI]

theorem retainedOutput_empty {ι α β : Type*} (q : ι → α → α → β) (z : α × α) :
    retainedOutput ∅ q z = (z.1, fun _ ↦ none) := by
  apply Prod.ext rfl
  funext j
  simp [retainedOutput, maskedCoordinateOutput]

end
end Erdos539Geometry
