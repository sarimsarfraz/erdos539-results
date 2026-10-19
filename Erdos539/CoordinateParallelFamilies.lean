/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinatePartitionTree

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
universe u
variable {ι : Type u}
local instance parallelFamilyDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace CoordinatePartitionTree

/-- Nodes of the fixed coordinate tree, before expanding their parallel fibers. -/
def Shape : {B : Finset ι} → CoordinatePartitionTree B → Type u
  | _, .leaf _ _ => PUnit
  | _, .split _ _ _ _ _ l r => PUnit ⊕ (l.Shape ⊕ r.Shape)

instance shapeFintype : {B : Finset ι} → (p : CoordinatePartitionTree B) → Fintype p.Shape
  | _, .leaf _ _ => inferInstanceAs (Fintype PUnit)
  | _, .split _ _ _ _ _ l r => by
    letI := shapeFintype l
    letI := shapeFintype r
    exact inferInstanceAs (Fintype (PUnit ⊕ (l.Shape ⊕ r.Shape)))

def shapeDepth : {B : Finset ι} → (p : CoordinatePartitionTree B) → p.Shape → ℕ
  | _, .leaf _ _ => fun _ ↦ 0
  | _, .split _ _ _ _ _ l r => fun q ↦ match q with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl q) => l.shapeDepth q + 1
    | Sum.inr (Sum.inr q) => r.shapeDepth q + 1

def shapeBlock : {B : Finset ι} → (p : CoordinatePartitionTree B) → p.Shape → Finset ι
  | _, .leaf B _ => fun _ ↦ B
  | _, .split B _ _ _ _ l r => fun q ↦ match q with
    | Sum.inl _ => B
    | Sum.inr (Sum.inl q) => l.shapeBlock q
    | Sum.inr (Sum.inr q) => r.shapeBlock q

def place : {B : Finset ι} → (p : CoordinatePartitionTree B) →
    (s : StationaryReferenceState (ι → ℝ)) → (p.realize s).Node → p.Shape
  | _, .leaf _ _, _ => fun _ ↦ PUnit.unit
  | _, .split _ _ _ _ _ l r, s => fun n ↦ match n with
    | Sum.inl _ => Sum.inl PUnit.unit
    | Sum.inr (Sum.inl ⟨y, n⟩) => Sum.inr (Sum.inl (l.place (s.fiber _ y) n))
    | Sum.inr (Sum.inr ⟨z, n⟩) => Sum.inr (Sum.inr (r.place (s.fiber _ z) n))

theorem depth_place {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) (n : (p.realize s).Node) :
    (p.realize s).depth n = p.shapeDepth (p.place s n) := by
  induction p generalizing s with
  | leaf B hc => rfl
  | split B I hI hi hj l r ihl ihr =>
    change (PUnit ⊕ ((Σ y, (l.realize (s.fiber (maskCoordinatesHom (B \ I)) y)).Node) ⊕
      (Σ z, (r.realize (s.fiber (maskCoordinatesHom I) z)).Node))) at n
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp [realize, StationaryParallelRecursion.depth, place, shapeDepth]
    · simpa only [realize, StationaryParallelRecursion.depth, place, shapeDepth] using congrArg (· + 1) (ihl _ n)
    · simpa only [realize, StationaryParallelRecursion.depth, place, shapeDepth] using congrArg (· + 1) (ihr _ n)

theorem block_place {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) (n : (p.realize s).Node) :
    p.nodeBlock s n = p.shapeBlock (p.place s n) := by
  induction p generalizing s with
  | leaf B hc => rfl
  | split B I hI hi hj l r ihl ihr =>
    change (PUnit ⊕ ((Σ y, (l.realize (s.fiber (maskCoordinatesHom (B \ I)) y)).Node) ⊕
      (Σ z, (r.realize (s.fiber (maskCoordinatesHom I) z)).Node))) at n
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp [nodeBlock, place, shapeBlock]
    · simpa only [nodeBlock, place, shapeBlock] using ihl _ n
    · simpa only [nodeBlock, place, shapeBlock] using ihr _ n

private theorem sum_ite_left_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) (b : α → Prop) [DecidablePred b] :
    (∑ x, if b x then c * f x else 0) = c * ∑ x, if b x then f x else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_ite, mul_zero]

/-- At each coordinate-tree node, its entire family of parallel fibers
has total original-law probability one. -/
theorem family_mass_one {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) (q : p.Shape) :
    finitePush (p.realize s).reach (p.place s) q = 1 := by
  induction p generalizing s with
  | leaf B hc =>
    change PUnit at q
    cases q
    unfold finitePush
    change (∑ n : PUnit, _) = 1
    simp [realize, StationaryParallelRecursion.reach, place]
  | split B I hI hi hj l r ihl ihr =>
    change PUnit ⊕ (l.Shape ⊕ r.Shape) at q
    unfold finitePush
    change (∑ n : PUnit ⊕ ((Σ y, (l.realize (s.fiber (maskCoordinatesHom (B \ I)) y)).Node) ⊕
      (Σ z, (r.realize (s.fiber (maskCoordinatesHom I) z)).Node)), _) = 1
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fintype.sum_sigma, Fintype.sum_unique, place, realize, StationaryParallelRecursion.reach]
    rcases q with q | (q | q)
    · cases q
      simp
    · simp only [Shape, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add, add_zero]
      simp_rw [sum_ite_left_mul]
      change (∑ y, s.sample (maskCoordinatesHom (B \ I)) y *
        finitePush (l.realize (s.fiber (maskCoordinatesHom (B \ I)) y)).reach
          (l.place (s.fiber (maskCoordinatesHom (B \ I)) y)) q) = 1
      simp_rw [ihl, mul_one]
      exact s.sample_sum _
    · simp only [Shape, Sum.inr.injEq, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add]
      simp_rw [sum_ite_left_mul]
      change (∑ z, s.sample (maskCoordinatesHom I) z *
        finitePush (r.realize (s.fiber (maskCoordinatesHom I) z)).reach
          (r.place (s.fiber (maskCoordinatesHom I) z)) q) = 1
      simp_rw [ihr, mul_one]
      exact s.sample_sum _

/-- Mean projected cost P_B over the whole parallel family at B. -/
def familyProjection {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) : p.Shape → ℝ :=
  finitePush (fun n ↦ (p.realize s).reach n * (p.realize s).projectionCharge n) (p.place s)

/-- Mean terminal cost E_B, zero at internal nodes. -/
def familyTerminal {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) : p.Shape → ℝ :=
  finitePush (fun n ↦ (p.realize s).reach n * (p.realize s).terminalCharge n) (p.place s)

/-- Equation (13a), grouped by the fixed coordinate tree rather than by
individual fibers. All weights are from the one original endpoint law. -/
theorem parallel_family_budget {B : Finset ι} (p : CoordinatePartitionTree B)
    (s : StationaryReferenceState (ι → ℝ)) :
    (∑ q : p.Shape, ((1 / 2 : ℝ) ^ (p.shapeDepth q + 1) * p.familyProjection s q +
      (1 / 2 : ℝ) ^ p.shapeDepth q * p.familyTerminal s q)) ≤ s.cost := by
  have he : (∑ q : p.Shape, ((1 / 2 : ℝ) ^ (p.shapeDepth q + 1) * p.familyProjection s q +
      (1 / 2 : ℝ) ^ p.shapeDepth q * p.familyTerminal s q)) =
      ∑ n, (p.realize s).reach n * ((1 / 2 : ℝ) ^ ((p.realize s).depth n + 1) *
        (p.realize s).projectionCharge n + (1 / 2 : ℝ) ^ (p.realize s).depth n * (p.realize s).terminalCharge n) := by
    rw [Finset.sum_add_distrib]
    simp only [familyProjection, familyTerminal]
    conv_lhs => arg 1; arg 2; ext q; rw [mul_comm]
    conv_lhs => arg 2; arg 2; ext q; rw [mul_comm]
    rw [finitePush_expectation, finitePush_expectation, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [p.depth_place s n]
    ring
  rw [he]
  exact p.depth_weighted_budget s

end CoordinatePartitionTree
end
end Erdos539Geometry
