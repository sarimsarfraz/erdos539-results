/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SeparatedNormAggregation

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
local instance separatedHierarchyFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A finite hierarchy of actual nonempty component partitions. Every
internal partition has separated unordered component-pair sums. Leaves
are actual subsets; there is no depth or equal-size restriction. -/
inductive SeparatedHierarchy : Finset G → Finset (Finset G) → Prop
  | leaf (S : Finset G) (hne : S.Nonempty) : SeparatedHierarchy S {S}
  | split (S : Finset G) (hne : S.Nonempty) (n : ℕ) (label : G → Fin n)
      (L : Fin n → Finset (Finset G)) (hsep : SeparatedSumLabels S label)
      (children : ∀ i, SeparatedHierarchy (fiber S label i) (L i)) :
      SeparatedHierarchy S (Finset.univ.biUnion L)

namespace SeparatedHierarchy
variable {S : Finset G} {L : Finset (Finset G)}

theorem root_nonempty (h : SeparatedHierarchy S L) : S.Nonempty := by
  cases h with
  | leaf _ h => exact h
  | split _ h _ _ _ _ _ => exact h

theorem leaf_nonempty_subset (h : SeparatedHierarchy S L) :
    ∀ T ∈ L, T.Nonempty ∧ T ⊆ S := by
  induction h with
  | leaf S hS =>
    intro T hT
    have he : T = S := Finset.mem_singleton.mp hT
    subst T
    exact ⟨hS, Finset.Subset.refl S⟩
  | split S _ n label L _ _ ih =>
    intro T hT
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hT
    have ht := ih i T hi
    exact ⟨ht.1, ht.2.trans (fun _ hx ↦ (mem_fiber.mp hx).1)⟩

theorem leaves_nonempty (h : SeparatedHierarchy S L) : L.Nonempty := by
  induction h with
  | leaf S _ => exact Finset.singleton_nonempty S
  | split S hS n label L _ _ ih =>
    obtain ⟨a, _⟩ := hS
    obtain ⟨T, hT⟩ := ih (label a)
    exact ⟨T, Finset.mem_biUnion.mpr ⟨label a, Finset.mem_univ _, hT⟩⟩

theorem component_leaves_disjoint {n : ℕ} (S : Finset G) (label : G → Fin n)
    (L : Fin n → Finset (Finset G))
    (children : ∀ i, SeparatedHierarchy (fiber S label i) (L i)) :
    ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise (fun i j ↦ Disjoint (L i) (L j)) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro T hi hj
  have hTi := (children i).leaf_nonempty_subset T hi
  have hTj := (children j).leaf_nonempty_subset T hj
  obtain ⟨a, ha⟩ := hTi.1
  have hai := (mem_fiber.mp (hTi.2 ha)).2
  have haj := (mem_fiber.mp (hTj.2 ha)).2
  exact hij (hai.symm.trans haj)

/-- The actual leaf sizes partition the root cardinality exactly. -/
theorem sum_leaf_card (h : SeparatedHierarchy S L) : ∑ T ∈ L, T.card = S.card := by
  induction h with
  | leaf S _ => simp
  | split S _ n label L _ children ih =>
    rw [Finset.sum_biUnion (component_leaves_disjoint S label L children)]
    simp_rw [ih]
    exact (Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ)
      (f := label) (fun _ _ ↦ Finset.mem_univ _)).symm

/-- Rational norm aggregation through the entire finite hierarchy. -/
theorem norm_power_le_sum_leaves (h : SeparatedHierarchy S L) :
    energyNorm S ^ (5 / 3 : ℝ) ≤ ∑ T ∈ L, energyNorm T ^ (5 / 3 : ℝ) := by
  induction h with
  | leaf S _ => simp
  | split S _ n label L hsep children ih =>
    rw [Finset.sum_biUnion (component_leaves_disjoint S label L children)]
    exact (energyNorm_separated_rational hsep).trans (Finset.sum_le_sum (fun i _ ↦ ih i))

end SeparatedHierarchy
end
end Erdos539Geometry
