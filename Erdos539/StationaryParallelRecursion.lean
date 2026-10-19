/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryReferenceState

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]
local instance parallelImageDecidableEq (s : StationaryReferenceState G) (φ : G →+ G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

/-- Both complete families of actual conditional fibers are retained.
No new Gibbs endpoint is chosen at an internal node. -/
inductive StationaryParallelRecursion : StationaryReferenceState G → Type u
  | leaf (s : StationaryReferenceState G) : StationaryParallelRecursion s
  | split (s : StationaryReferenceState G) (φ ψ : G →+ G)
      (left : (y : s.support.image φ) → StationaryParallelRecursion (s.fiber φ y))
      (right : (z : s.support.image ψ) → StationaryParallelRecursion (s.fiber ψ z)) :
        StationaryParallelRecursion s

namespace StationaryParallelRecursion

/-- Recursive form of the depth-weighted sum, including all terminal costs. -/
def totalCost : {s : StationaryReferenceState G} → StationaryParallelRecursion s → ℝ
  | _, .leaf s => s.cost
  | _, .split s φ ψ l r => ((s.image φ).cost + (s.image ψ).cost +
      (∑ y, s.sample φ y * (l y).totalCost) + (∑ z, s.sample ψ z * (r z).totalCost)) / 2

theorem totalCost_nonneg {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) :
    0 ≤ t.totalCost := by
  induction t with
  | leaf s => exact s.cost_nonneg
  | split s φ ψ l r ihl ihr =>
    exact div_nonneg (add_nonneg (add_nonneg (add_nonneg
      (s.image φ).cost_nonneg (s.image ψ).cost_nonneg)
      (Finset.sum_nonneg fun y _ ↦ mul_nonneg (s.sample_nonneg φ y) (ihl y)))
      (Finset.sum_nonneg fun z _ ↦ mul_nonneg (s.sample_nonneg ψ z) (ihr z))) (by norm_num)

theorem totalCost_le {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) :
    t.totalCost ≤ s.cost := by
  induction t with
  | leaf s => exact le_rfl
  | split s φ ψ l r ihl ihr =>
    have hl := Finset.sum_le_sum (s := Finset.univ) fun y _ ↦ mul_le_mul_of_nonneg_left (ihl y) (s.sample_nonneg φ y)
    have hr := Finset.sum_le_sum (s := Finset.univ) fun z _ ↦ mul_le_mul_of_nonneg_left (ihr z) (s.sample_nonneg ψ z)
    have h := s.cost_two_cuts φ ψ
    change (_ + _ + _ + _) / 2 ≤ _
    linarith

/-- Every node in every actual fiber, including the root and all leaves. -/
def Node : {s : StationaryReferenceState G} → StationaryParallelRecursion s → Type u
  | _, .leaf _ => PUnit
  | _, .split _ _ _ l r => PUnit ⊕ ((Σ y, (l y).Node) ⊕ (Σ z, (r z).Node))

instance nodeFintype : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → Fintype t.Node
  | _, .leaf _ => inferInstanceAs (Fintype PUnit)
  | _, .split _ _ _ l r => by
    letI := fun y ↦ nodeFintype (l y)
    letI := fun z ↦ nodeFintype (r z)
    exact inferInstanceAs (Fintype (PUnit ⊕ ((Σ y, (l y).Node) ⊕ (Σ z, (r z).Node))))

def depth : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → t.Node → ℕ
  | _, .leaf _ => fun _ ↦ 0
  | _, .split _ _ _ l r => fun n ↦ match n with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl ⟨y, n⟩) => (l y).depth n + 1
    | Sum.inr (Sum.inr ⟨z, n⟩) => (r z).depth n + 1

/-- Product of actual conditional probabilities along a branch.
The dyadic depth coefficient is kept separate. -/
def reach : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → t.Node → ℝ
  | _, .leaf _ => fun _ ↦ 1
  | _, .split s φ ψ l r => fun n ↦ match n with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl ⟨y, n⟩) => s.sample φ y * (l y).reach n
    | Sum.inr (Sum.inr ⟨z, n⟩) => s.sample ψ z * (r z).reach n

def projectionCharge : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → t.Node → ℝ
  | _, .leaf _ => fun _ ↦ 0
  | _, .split s φ ψ l r => fun n ↦ match n with
    | Sum.inl _ => (s.image φ).cost + (s.image ψ).cost
    | Sum.inr (Sum.inl ⟨y, n⟩) => (l y).projectionCharge n
    | Sum.inr (Sum.inr ⟨z, n⟩) => (r z).projectionCharge n

def terminalCharge : {s : StationaryReferenceState G} → (t : StationaryParallelRecursion s) → t.Node → ℝ
  | _, .leaf s => fun _ ↦ s.cost
  | _, .split _ _ _ l r => fun n ↦ match n with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl ⟨y, n⟩) => (l y).terminalCharge n
    | Sum.inr (Sum.inr ⟨z, n⟩) => (r z).terminalCharge n

theorem reach_nonneg {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node) :
    0 ≤ t.reach n := by
  induction t with
  | leaf s => simp only [reach]; exact zero_le_one
  | split s φ ψ l r ihl ihr =>
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simp only [reach]; exact zero_le_one
    · simpa only [reach] using mul_nonneg (s.sample_nonneg φ y) (ihl y n)
    · simpa only [reach] using mul_nonneg (s.sample_nonneg ψ z) (ihr z n)

theorem charges_nonneg {s : StationaryReferenceState G} (t : StationaryParallelRecursion s) (n : t.Node) :
    0 ≤ t.projectionCharge n ∧ 0 ≤ t.terminalCharge n := by
  induction t with
  | leaf s => simpa only [projectionCharge, terminalCharge, le_refl, true_and] using s.cost_nonneg
  | split s φ ψ l r ihl ihr =>
    rcases n with n | (⟨y, n⟩ | ⟨z, n⟩)
    · simpa only [projectionCharge, terminalCharge, le_refl, and_true] using
        add_nonneg (s.image φ).cost_nonneg (s.image ψ).cost_nonneg
    · simpa only [projectionCharge, terminalCharge] using ihl y n
    · simpa only [projectionCharge, terminalCharge] using ihr z n

end StationaryParallelRecursion
end
end Erdos539Geometry
