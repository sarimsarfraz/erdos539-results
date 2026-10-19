/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryParallelBudget

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

namespace StationaryParallelRecursion

def nodeState : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → t.Node → StationaryReferenceState G
  | _, .leaf s => fun _ ↦ s
  | _, .split s _ _ l r => fun n ↦ match n with
    | Sum.inl _ => s
    | Sum.inr (Sum.inl ⟨y, n⟩) => (l y).nodeState n
    | Sum.inr (Sum.inr ⟨z, n⟩) => (r z).nodeState n

theorem node_subset {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node) :
    (t.nodeState n).support ⊆ s.support := by
  induction t with
  | leaf s => exact Finset.Subset.refl _
  | split s φ ψ l r ihl ihr =>
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp only [nodeState]; exact Finset.Subset.refl _
    · intro x hx
      simp only [nodeState] at hx
      exact (mem_fiber.mp (ihl y n hx)).1
    · intro x hx
      simp only [nodeState] at hx
      exact (mem_fiber.mp (ihr z n hx)).1

def nodeEmbedding {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node)
    (x : (t.nodeState n).support) : s.support := ⟨x.val, t.node_subset n x.property⟩

/-- The reference has its own branch mass; it is conditioned on exactly
the same subsets as the original endpoint law. -/
def referenceReach : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → t.Node → ℝ
  | _, .leaf _ => fun _ ↦ 1
  | _, .split s φ ψ l r => fun n ↦ match n with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl ⟨y, n⟩) => (s.image φ).reference y * (l y).referenceReach n
    | Sum.inr (Sum.inr ⟨z, n⟩) => (s.image ψ).reference z * (r z).referenceReach n

theorem referenceReach_pos {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node) :
    0 < t.referenceReach n := by
  induction t with
  | leaf s => exact zero_lt_one
  | split s φ ψ l r ihl ihr =>
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp only [referenceReach]; exact zero_lt_one
    · simpa only [referenceReach] using mul_pos ((s.image φ).reference_pos y) (ihl y n)
    · simpa only [referenceReach] using mul_pos ((s.image ψ).reference_pos z) (ihr z n)

/-- Pointwise disintegration all the way back to the original root law. -/
theorem node_law_reconstruct {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node)
    (x : (t.nodeState n).support) : s.law (t.nodeEmbedding n x) = t.reach n * (t.nodeState n).law x := by
  induction t with
  | leaf s => simp [reach, nodeState, nodeEmbedding]
  | split s φ ψ l r ihl ihr =>
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp only [nodeState] at x
      simp [reach, nodeState, nodeEmbedding]
    · simp only [nodeState] at x
      simp only [reach, nodeState, nodeEmbedding]
      have h := s.fiber_law_reconstruct φ y ((l y).nodeEmbedding n x)
      change s.sample φ y * (s.fiber φ y).law ((l y).nodeEmbedding n x) = _ at h
      rw [ihl y n x] at h
      change _ = (s.sample φ y * (l y).reach n) * ((l y).nodeState n).law x
      exact (mul_assoc _ _ _).trans h |>.symm
    · simp only [nodeState] at x
      simp only [reach, nodeState, nodeEmbedding]
      have h := s.fiber_law_reconstruct ψ z ((r z).nodeEmbedding n x)
      change s.sample ψ z * (s.fiber ψ z).law ((r z).nodeEmbedding n x) = _ at h
      rw [ihr z n x] at h
      change _ = (s.sample ψ z * (r z).reach n) * ((r z).nodeState n).law x
      exact (mul_assoc _ _ _).trans h |>.symm

theorem node_reference_reconstruct {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node)
    (x : (t.nodeState n).support) : s.reference (t.nodeEmbedding n x) =
      t.referenceReach n * (t.nodeState n).reference x := by
  induction t with
  | leaf s => simp [referenceReach, nodeState, nodeEmbedding]
  | split s φ ψ l r ihl ihr =>
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp only [nodeState] at x
      simp [referenceReach, nodeState, nodeEmbedding]
    · simp only [nodeState] at x
      simp only [referenceReach, nodeState, nodeEmbedding]
      have h := imageFiberReference_reconstruct s.support φ s.reference s.reference_pos y ((l y).nodeEmbedding n x)
      change (s.image φ).reference y * (s.fiber φ y).reference ((l y).nodeEmbedding n x) = _ at h
      rw [ihl y n x] at h
      change _ = ((s.image φ).reference y * (l y).referenceReach n) * ((l y).nodeState n).reference x
      exact (mul_assoc _ _ _).trans h |>.symm
    · simp only [nodeState] at x
      simp only [referenceReach, nodeState, nodeEmbedding]
      have h := imageFiberReference_reconstruct s.support ψ s.reference s.reference_pos z ((r z).nodeEmbedding n x)
      change (s.image ψ).reference z * (s.fiber ψ z).reference ((r z).nodeEmbedding n x) = _ at h
      rw [ihr z n x] at h
      change _ = ((s.image ψ).reference z * (r z).referenceReach n) * ((r z).nodeState n).reference x
      exact (mul_assoc _ _ _).trans h |>.symm

/-- A node's reach is exactly its support mass in the fixed original law. -/
theorem reach_eq_root_mass {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node) :
    t.reach n = ∑ x, s.law (t.nodeEmbedding n x) := by
  simp_rw [node_law_reconstruct, ← Finset.mul_sum, (t.nodeState n).law_sum, mul_one]

theorem referenceReach_eq_root_mass {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node) :
    t.referenceReach n = ∑ x, s.reference (t.nodeEmbedding n x) := by
  simp_rw [node_reference_reconstruct, ← Finset.mul_sum, (t.nodeState n).reference_sum, mul_one]

/-- Full-support roots recover strictly positive reach at every node. -/
theorem reach_pos_of_root_law_pos {s : StationaryReferenceState G} (t : StationaryParallelRecursion s)
    (hs : ∀ x, 0 < s.law x) (n : t.Node) : 0 < t.reach n := by
  rw [t.reach_eq_root_mass n]
  obtain ⟨a, ha⟩ := (t.nodeState n).nonempty
  exact (hs (t.nodeEmbedding n ⟨a, ha⟩)).trans_le (Finset.single_le_sum
    (fun x _ ↦ s.law_nonneg (t.nodeEmbedding n x)) (Finset.mem_univ (⟨a, ha⟩ : (t.nodeState n).support)))

/-- Every original endpoint atom in a zero-reach node is itself zero. -/
theorem root_law_zero_of_zero_reach {s : StationaryReferenceState G} (t : StationaryParallelRecursion s)
    (n : t.Node) (hm : t.reach n = 0) (x : (t.nodeState n).support) : s.law (t.nodeEmbedding n x) = 0 := by
  rw [node_law_reconstruct, hm, zero_mul]

/-- On positive-mass nodes, the endpoint is the literal normalized
restriction of the fixed root law. Zero-mass node laws carry no cost. -/
theorem node_law_eq_root_conditional {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node)
    (hm : t.reach n ≠ 0) (x : (t.nodeState n).support) : (t.nodeState n).law x =
      s.law (t.nodeEmbedding n x) / (∑ z, s.law (t.nodeEmbedding n z)) := by
  rw [← reach_eq_root_mass, node_law_reconstruct]
  exact (mul_div_cancel_left₀ _ hm).symm

theorem node_reference_eq_root_conditional {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node)
    (x : (t.nodeState n).support) : (t.nodeState n).reference x =
      s.reference (t.nodeEmbedding n x) / (∑ z, s.reference (t.nodeEmbedding n z)) := by
  rw [← referenceReach_eq_root_mass, node_reference_reconstruct]
  exact (mul_div_cancel_left₀ _ (t.referenceReach_pos n).ne').symm

end StationaryParallelRecursion
end
end Erdos539Geometry
