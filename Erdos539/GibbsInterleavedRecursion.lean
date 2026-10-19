/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsComponentState
import Erdos539.GibbsRecursionBudget

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]
local instance interleavedFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance interleavedImageDecidableEq (s : GibbsReference G) (φ : G → G) :
    DecidableEq (s.support.image φ) := Classical.decEq _
local instance interleavedLabelDecidableEq (s : GibbsReference G) (n : ℕ) (label : G → Fin n) :
    DecidableEq (s.support.image label) := Classical.decEq _

/-- Actual finite recursion interleaving two-child additive cuts with
one-child separated-component selection. Every component node carries
the real separation proof for its current support. -/
inductive GibbsInterleavedRecursion : GibbsReference G → Type u
  | leaf (s : GibbsReference G) : GibbsInterleavedRecursion s
  | cut (s : GibbsReference G) (φ : G →+ G)
      (projection : GibbsInterleavedRecursion (s.image φ))
      (fibers : (y : s.support.image φ) → GibbsInterleavedRecursion (s.fiber φ y)) : GibbsInterleavedRecursion s
  | select (s : GibbsReference G) (n : ℕ) (label : G → Fin n)
      (separated : SeparatedSumLabels s.support label)
      (components : (i : s.support.image label) → GibbsInterleavedRecursion (s.component label i)) :
        GibbsInterleavedRecursion s

namespace GibbsInterleavedRecursion

def Outcome : {s : GibbsReference G} → GibbsInterleavedRecursion s → Type u
  | _, .leaf _ => PUnit
  | _, .cut _ _ p f => p.Outcome × (Σ y, (f y).Outcome)
  | _, .select _ _ _ _ f => Σ i, (f i).Outcome

instance outcomeFintype : {s : GibbsReference G} → (t : GibbsInterleavedRecursion s) → Fintype t.Outcome
  | _, .leaf _ => inferInstanceAs (Fintype PUnit)
  | _, .cut _ _ p f => by
    letI := outcomeFintype p
    letI := fun y ↦ outcomeFintype (f y)
    exact inferInstanceAs (Fintype (p.Outcome × (Σ y, (f y).Outcome)))
  | _, .select _ _ _ _ f => by
    letI := fun i ↦ outcomeFintype (f i)
    exact inferInstanceAs (Fintype (Σ i, (f i).Outcome))

def probability : {s : GibbsReference G} → (t : GibbsInterleavedRecursion s) → t.Outcome → ℝ
  | _, .leaf _, _ => 1
  | _, .cut s φ p f, x => p.probability x.1 * (s.sample φ x.2.1 * (f x.2.1).probability x.2.2)
  | _, .select s _ label _ f, x => s.componentSample label x.1 * (f x.1).probability x.2

theorem probability_pos {s : GibbsReference G} (t : GibbsInterleavedRecursion s) (x : t.Outcome) :
    0 < t.probability x := by
  induction t with
  | leaf s => exact zero_lt_one
  | cut s φ p f ihp ihf => exact mul_pos (ihp x.1) (mul_pos (s.sample_pos φ x.2.1) (ihf x.2.1 x.2.2))
  | select s n label hsep f ih => exact mul_pos (s.componentSample_pos label x.1) (ih x.1 x.2)

theorem probability_sum {s : GibbsReference G} (t : GibbsInterleavedRecursion s) : ∑ x, t.probability x = 1 := by
  induction t with
  | leaf s => simp [probability, Outcome]
  | cut s φ p f ihp ihf =>
    change (∑ x : p.Outcome × (Σ y, (f y).Outcome), p.probability x.1 *
      (s.sample φ x.2.1 * (f x.2.1).probability x.2.2)) = 1
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_sigma, ← Finset.mul_sum, ihf, mul_one, s.sample_sum, ihp]
  | select s n label hsep f ih =>
    change (∑ x : (Σ i, (f i).Outcome), s.componentSample label x.1 * (f x.1).probability x.2) = 1
    simp only [Fintype.sum_sigma, ← Finset.mul_sum, ih, mul_one, s.componentSample_sum]

def cost (coordinateCharge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ) :
    {s : GibbsReference G} → (t : GibbsInterleavedRecursion s) → t.Outcome → ℝ
  | _, .leaf s, _ => s.deficit
  | _, .cut s φ p f, x => p.cost coordinateCharge x.1 + coordinateCharge s φ x.2.1 + (f x.2.1).cost coordinateCharge x.2.2
  | _, .select s _ label _ f, x => s.componentCharge label x.1 + (f x.1).cost coordinateCharge x.2

def expectedCost (coordinateCharge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ) :
    {s : GibbsReference G} → GibbsInterleavedRecursion s → ℝ
  | _, .leaf s => s.deficit
  | _, .cut s φ p f => p.expectedCost coordinateCharge +
      ∑ y, s.sample φ y * (coordinateCharge s φ y + (f y).expectedCost coordinateCharge)
  | _, .select s _ label _ f =>
      ∑ i, s.componentSample label i * (s.componentCharge label i + (f i).expectedCost coordinateCharge)

theorem expectation_cost
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    {s : GibbsReference G} (t : GibbsInterleavedRecursion s) :
    (∑ x, t.probability x * t.cost charge x) = t.expectedCost charge := by
  induction t with
  | leaf s => simp [probability, cost, expectedCost, Outcome]
  | cut s φ p f ihp ihf =>
    change (∑ x : p.Outcome × (Σ y, (f y).Outcome),
      (p.probability x.1 * (s.sample φ x.2.1 * (f x.2.1).probability x.2.2)) *
        (p.cost charge x.1 + charge s φ x.2.1 + (f x.2.1).cost charge x.2.2)) = _
    rw [finite_branch_expectation p.probability (s.sample φ) (fun y ↦ (f y).probability)
      p.probability_sum (s.sample_sum φ) (fun y ↦ (f y).probability_sum)
      (p.cost charge) (charge s φ) (fun y ↦ (f y).cost charge), ihp]
    simp_rw [ihf]
    rfl
  | select s n label hsep f ih =>
    change (∑ x : (Σ i, (f i).Outcome), (s.componentSample label x.1 * (f x.1).probability x.2) *
      (s.componentCharge label x.1 + (f x.1).cost charge x.2)) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = s.componentSample label i *
          (s.componentCharge label i * (∑ x, (f i).probability x) +
            ∑ x, (f i).probability x * (f i).cost charge x) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring
      _ = _ := by rw [(f i).probability_sum, ih, mul_one]

end GibbsInterleavedRecursion
end
end Erdos539Geometry
