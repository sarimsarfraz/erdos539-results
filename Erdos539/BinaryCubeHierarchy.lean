/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.BinaryCubeNorm
import Erdos539.SeparatedHierarchy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
local instance binaryHierarchyIntDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance binaryHierarchyProdDecidableEq {α β : Type*} : DecidableEq (α × β) := Classical.decEq _
local instance binaryHierarchyFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace SeparatedHierarchy
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

omit [DecidableEq H] in
/-- Adding a constant coordinate transports the actual hierarchy and leaves. -/
theorem pair_const {S : Finset G} {L : Finset (Finset G)}
    (h : SeparatedHierarchy S L) (a : H) :
    SeparatedHierarchy (S.image (fun x ↦ (a, x)))
      (L.image (fun T ↦ T.image (fun x ↦ (a, x)))) := by
  induction h with
  | leaf S hS =>
    simpa only [Finset.image_singleton] using
      SeparatedHierarchy.leaf (S.image (fun x ↦ (a, x))) (hS.image _)
  | split S hS n label L hsep children ih =>
    have hfiber : ∀ i, fiber (S.image (fun x ↦ (a, x))) (fun x ↦ label x.2) i =
        (fiber S label i).image (fun x ↦ (a, x)) := by
      intro i
      ext p
      simp only [mem_fiber, Finset.mem_image]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hi⟩
        exact ⟨x, ⟨hx, hi⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hi⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hi⟩
    have hs : SeparatedSumLabels (S.image (fun x ↦ (a, x))) (fun x ↦ label x.2) := by
      intro x hx y hy z hz w hw he
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
      exact hsep x' hx' y' hy' z' hz' w' hw' (congrArg Prod.snd he)
    rw [Finset.biUnion_image]
    apply SeparatedHierarchy.split _ (hS.image _) n (fun x ↦ label x.2) _ hs
    intro i
    rw [hfiber]
    exact ih i

end SeparatedHierarchy

/-- Every two-point integer sum determines its unordered endpoints. -/
theorem binary_sum_unordered {a b c d : ℤ}
    (ha : a ∈ ({0, 1} : Finset ℤ)) (hb : b ∈ ({0, 1} : Finset ℤ))
    (hc : c ∈ ({0, 1} : Finset ℤ)) (hd : d ∈ ({0, 1} : Finset ℤ))
    (he : a + b = c + d) : SameUnorderedPair a b c d := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    norm_num [SameUnorderedPair] at *

def binaryLabel (x : ℤ) : Fin 2 := if x = 0 then 0 else 1

/-- Successive binary coordinate splits are a genuine separated hierarchy
whose actual leaves are exactly the singletons of the cube. -/
theorem binaryCube_singleton_hierarchy (n : ℕ) :
    SeparatedHierarchy (binaryCube n) ((binaryCube n).image (fun x ↦ {x})) := by
  induction n with
  | zero =>
    simpa only [binaryCube, Finset.image_singleton] using
      SeparatedHierarchy.leaf ({0} : Finset ℤ) (Finset.singleton_nonempty 0)
  | succ n ih =>
    let S := binaryCube n
    let label : ℤ × BinaryAmbient n → Fin 2 := fun x ↦ binaryLabel x.1
    let L : Fin 2 → Finset (Finset (ℤ × BinaryAmbient n)) := fun i ↦
      (S.image (fun x ↦ {x})).image (fun T : Finset (BinaryAmbient n) ↦ T.image (fun x ↦ ((i.val : ℤ), x)))
    have hsep : SeparatedSumLabels (({0, 1} : Finset ℤ) ×ˢ S) label := by
      intro a ha b hb c hc d hd he
      have hs := binary_sum_unordered (Finset.mem_product.mp ha).1
        (Finset.mem_product.mp hb).1 (Finset.mem_product.mp hc).1
        (Finset.mem_product.mp hd).1 (congrArg Prod.fst he)
      rcases hs with ⟨hac, hbd⟩ | ⟨had, hbc⟩
      · exact Or.inl ⟨congrArg binaryLabel hac, congrArg binaryLabel hbd⟩
      · exact Or.inr ⟨congrArg binaryLabel had, congrArg binaryLabel hbc⟩
    have hfiber : ∀ i : Fin 2, fiber (({0, 1} : Finset ℤ) ×ˢ S) label i =
        S.image (fun x ↦ ((i.val : ℤ), x)) := by
      intro i
      fin_cases i <;> ext p <;>
        simp [mem_fiber, label, binaryLabel, Finset.mem_product, Prod.ext_iff] <;> aesop
    have hleaves : Finset.univ.biUnion L =
        ((({0, 1} : Finset ℤ) ×ˢ S).image (fun x ↦ {x})) := by
      ext T
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, L, Finset.mem_image,
        Finset.mem_product]
      constructor
      · rintro ⟨i, U, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨((i.val : ℤ), x), ⟨?_, hx⟩, rfl⟩
        fin_cases i <;> simp
      · rintro ⟨⟨i, x⟩, ⟨hi, hx⟩, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact ⟨0, {x}, ⟨x, hx, rfl⟩, by simp⟩
        · exact ⟨1, {x}, ⟨x, hx, rfl⟩, by simp⟩
    change SeparatedHierarchy (({0, 1} : Finset ℤ) ×ˢ S)
      ((({0, 1} : Finset ℤ) ×ˢ S).image (fun x ↦ {x}))
    rw [← hleaves]
    apply SeparatedHierarchy.split _ (by exact (binaryCube_nonempty (n + 1))) 2 label L hsep
    intro i
    rw [hfiber]
    exact ih.pair_const (i.val : ℤ)

end
end Erdos539Geometry
