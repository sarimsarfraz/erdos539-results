/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryParallelRecursion

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

namespace StationaryParallelRecursion

/-- Recursively assigned contribution of each individual actual node. -/
def weightedCost : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → t.Node → ℝ
  | _, .leaf s => fun _ ↦ s.cost
  | _, .split s φ ψ l r => fun n ↦ match n with
    | Sum.inl _ => ((s.image φ).cost + (s.image ψ).cost) / 2
    | Sum.inr (Sum.inl ⟨y, n⟩) => s.sample φ y * (l y).weightedCost n / 2
    | Sum.inr (Sum.inr ⟨z, n⟩) => s.sample ψ z * (r z).weightedCost n / 2

theorem weightedCost_eq {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node) :
    t.weightedCost n = t.reach n *
      ((1 / 2 : ℝ) ^ (t.depth n + 1) * t.projectionCharge n + (1 / 2 : ℝ) ^ t.depth n * t.terminalCharge n) := by
  induction t with
  | leaf s => simp [weightedCost, reach, depth, projectionCharge, terminalCharge]
  | split s φ ψ l r ihl ihr =>
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp [weightedCost, reach, depth, projectionCharge, terminalCharge, div_eq_mul_inv, mul_comm]
    · simp only [weightedCost, reach, depth, projectionCharge, terminalCharge, ihl, pow_succ]
      ring
    · simp only [weightedCost, reach, depth, projectionCharge, terminalCharge, ihr, pow_succ]
      ring

theorem weightedCost_sum {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) :
    (∑ n, t.weightedCost n) = t.totalCost := by
  induction t with
  | leaf s => simp [Node, weightedCost, totalCost]
  | split s φ ψ l r ihl ihr =>
    change (∑ n : PUnit ⊕ ((Σ y, (l y).Node) ⊕ (Σ z, (r z).Node)), _) =
      ((s.image φ).cost + (s.image ψ).cost +
        (∑ y, s.sample φ y * (l y).totalCost) + (∑ z, s.sample ψ z * (r z).totalCost)) / 2
    simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_unique, weightedCost]
    simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, ihl, ihr]
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring

/-- The literal sum over all internal nodes and all terminal fibers.
Projection costs have coefficient 2^(-depth-1), terminal costs 2^(-depth). -/
theorem depth_weighted_budget {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) :
    (∑ n, t.reach n * ((1 / 2 : ℝ) ^ (t.depth n + 1) * t.projectionCharge n +
      (1 / 2 : ℝ) ^ t.depth n * t.terminalCharge n)) ≤ s.cost := by
  simp_rw [← weightedCost_eq]
  rw [weightedCost_sum]
  exact t.totalCost_le

theorem gibbs_depth_weighted_budget (s : GibbsReference G)
    (t : StationaryParallelRecursion (StationaryReferenceState.gibbsRoot s)) :
    (∑ n, t.reach n * ((1 / 2 : ℝ) ^ (t.depth n + 1) * t.projectionCharge n +
      (1 / 2 : ℝ) ^ t.depth n * t.terminalCharge n)) ≤ s.deficit := by
  have h := t.depth_weighted_budget
  rwa [StationaryReferenceState.gibbsRoot_cost] at h

end StationaryParallelRecursion
end
end Erdos539Geometry
