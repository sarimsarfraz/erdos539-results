/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryParallelProvenance
import Erdos539.StationaryCoordinateFibers

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
universe u
variable {ι : Type u}
local instance partitionVectorDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- A fixed binary partition of the physical coordinates. It does not
depend on which parallel fiber is visited. Leaves may be any nonempty blocks. -/
inductive CoordinatePartitionTree : Finset ι → Type u
  | leaf (B : Finset ι) (hB : B.Nonempty) : CoordinatePartitionTree B
  | split (B I : Finset ι) (hI : I ⊆ B) (hi : I.Nonempty) (hj : (B \ I).Nonempty)
      (left : CoordinatePartitionTree I) (right : CoordinatePartitionTree (B \ I)) : CoordinatePartitionTree B

namespace CoordinatePartitionTree

theorem exists_tree (B : Finset ι) (hB : B.Nonempty) : Nonempty (CoordinatePartitionTree B) := by
  induction B using Finset.strongInductionOn with
  | _ B ih =>
    by_cases hcard : B.card = 1
    · exact ⟨.leaf B hB⟩
    obtain ⟨i, hi⟩ := hB
    have hIB : ({i} : Finset ι) ⊆ B := Finset.singleton_subset_iff.mpr hi
    have hJsmall : B \ {i} ⊂ B := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro he
      have hmem : i ∈ B \ {i} := he.symm ▸ hi
      simp at hmem
    have hJ : (B \ {i}).Nonempty := by
      apply Finset.card_pos.mp
      have hc := Finset.card_sdiff_add_card_eq_card hIB
      have hb : 0 < B.card := Finset.card_pos.mpr ⟨i, hi⟩
      simp only [Finset.card_singleton] at hc
      omega
    obtain ⟨r⟩ := ih (B \ {i}) hJsmall hJ
    exact ⟨.split B {i} hIB (Finset.singleton_nonempty i) hJ (.leaf {i} (Finset.singleton_nonempty i)) r⟩

/-- Realize the same partition tree on every actual parallel fiber of
both complementary masks. Both original laws are conditioned literally. -/
def realize : {B : Finset ι} → CoordinatePartitionTree B →
    (s : StationaryReferenceState (ι → ℝ)) → StationaryParallelRecursion s
  | _, .leaf _ _, s => .leaf s
  | _, .split B I _ _ _ l r, s => .split s (maskCoordinatesHom (B \ I)) (maskCoordinatesHom I)
      (fun y ↦ l.realize (s.fiber (maskCoordinatesHom (B \ I)) y))
      (fun z ↦ r.realize (s.fiber (maskCoordinatesHom I) z))

/-- Each actual node's physical block, retaining the original coordinates. -/
def nodeBlock : {B : Finset ι} → (p : CoordinatePartitionTree B) →
    (s : StationaryReferenceState (ι → ℝ)) → (p.realize s).Node → Finset ι
  | _, .leaf B _, _ => fun _ ↦ B
  | _, .split B _ _ _ _ l r, s => fun n ↦ match n with
    | Sum.inl _ => B
    | Sum.inr (Sum.inl ⟨y, n⟩) => l.nodeBlock (s.fiber _ y) n
    | Sum.inr (Sum.inr ⟨z, n⟩) => r.nodeBlock (s.fiber _ z) n

theorem node_fullOutside {B : Finset ι} (p : CoordinatePartitionTree B)
    (root s : StationaryReferenceState (ι → ℝ)) (h : root.FullOutsideFiber s B)
    (n : (p.realize s).Node) : root.FullOutsideFiber ((p.realize s).nodeState n) (p.nodeBlock s n) := by
  induction p generalizing s with
  | leaf B hcard => simpa only [realize, nodeBlock, StationaryParallelRecursion.nodeState] using h
  | split B I hI hi hj l r ihl ihr =>
    change (PUnit ⊕ ((Σ y, (l.realize (s.fiber (maskCoordinatesHom (B \ I)) y)).Node) ⊕
      (Σ z, (r.realize (s.fiber (maskCoordinatesHom I) z)).Node))) at n
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simpa only [realize, nodeBlock, StationaryParallelRecursion.nodeState] using h
    · have hf := root.fiber_fullOutside h (B \ I) y
      rw [Finset.sdiff_sdiff_eq_self hI] at hf
      simpa only [realize, nodeBlock, StationaryParallelRecursion.nodeState] using ihl _ hf n
    · simpa only [realize, nodeBlock, StationaryParallelRecursion.nodeState] using
        ihr _ (root.fiber_fullOutside h I z) n

theorem node_fullOutside_root {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) (h : s.FixedOutside B) (n : (p.realize s).Node) :
    s.FullOutsideFiber ((p.realize s).nodeState n) (p.nodeBlock s n) :=
  p.node_fullOutside s s (s.fullOutsideFiber_self B h) n

/-- The full weighted parallel-family budget for any fixed partition tree. -/
theorem depth_weighted_budget {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) :
    (∑ n, (p.realize s).reach n *
      ((1 / 2 : ℝ) ^ ((p.realize s).depth n + 1) * (p.realize s).projectionCharge n +
        (1 / 2 : ℝ) ^ (p.realize s).depth n * (p.realize s).terminalCharge n)) ≤ s.cost :=
  (p.realize s).depth_weighted_budget

end CoordinatePartitionTree
end
end Erdos539Geometry
