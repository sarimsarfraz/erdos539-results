/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsReferenceState

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]
local instance recursionImageDecidableEq (s : GibbsReference G) (φ : G →+ G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

/-- A finite adaptive recursion on literal additive images and fibers.
The projection and every possible fiber have their own continued tree.
Coordinate projections padded by zero are additive endomorphisms. -/
inductive GibbsRecursion : GibbsReference G → Type u
  | leaf (s : GibbsReference G) : GibbsRecursion s
  | cut (s : GibbsReference G) (φ : G →+ G)
      (projection : GibbsRecursion (s.image φ))
      (fibers : (y : s.support.image φ) → GibbsRecursion (s.fiber φ y)) : GibbsRecursion s

namespace GibbsRecursion

/-- One realized tree retains the whole projected child and chooses one
actual fiber at every cut, recursively in both branches. -/
def Outcome : {s : GibbsReference G} → GibbsRecursion s → Type u
  | _, .leaf _ => PUnit
  | _, .cut _ _ p f => p.Outcome × (Σ y, (f y).Outcome)

instance outcomeFintype : {s : GibbsReference G} → (t : GibbsRecursion s) → Fintype t.Outcome
  | _, .leaf _ => inferInstanceAs (Fintype PUnit)
  | _, .cut _ _ p f => by
    letI := outcomeFintype p
    letI := fun y ↦ outcomeFintype (f y)
    exact inferInstanceAs (Fintype (p.Outcome × (Σ y, (f y).Outcome)))

def probability : {s : GibbsReference G} → (t : GibbsRecursion s) → t.Outcome → ℝ
  | _, .leaf _, _ => 1
  | _, .cut s φ p f, x => p.probability x.1 * (s.sample φ x.2.1 * (f x.2.1).probability x.2.2)

theorem probability_pos {s : GibbsReference G} (t : GibbsRecursion s) (x : t.Outcome) :
    0 < t.probability x := by
  induction t with
  | leaf s => exact zero_lt_one
  | cut s φ p f ihp ihf => exact mul_pos (ihp x.1) (mul_pos (s.sample_pos φ x.2.1) (ihf x.2.1 x.2.2))

theorem probability_sum {s : GibbsReference G} (t : GibbsRecursion s) : ∑ x, t.probability x = 1 := by
  induction t with
  | leaf s => simp [probability, Outcome]
  | cut s φ p f ihp ihf =>
    change (∑ x : p.Outcome × (Σ y, (f y).Outcome), p.probability x.1 *
      (s.sample φ x.2.1 * (f x.2.1).probability x.2.2)) = 1
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_sigma, ← Finset.mul_sum, ihf, mul_one, s.sample_sum, ihp]

def cost (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (terminal : GibbsReference G → ℝ) : {s : GibbsReference G} → (t : GibbsRecursion s) → t.Outcome → ℝ
  | _, .leaf s, _ => terminal s
  | _, .cut s φ p f, x => p.cost charge terminal x.1 + charge s φ x.2.1 + (f x.2.1).cost charge terminal x.2.2

def expectedCost (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    (terminal : GibbsReference G → ℝ) : {s : GibbsReference G} → GibbsRecursion s → ℝ
  | _, .leaf s => terminal s
  | _, .cut s φ p f => p.expectedCost charge terminal +
      ∑ y, s.sample φ y * (charge s φ y + (f y).expectedCost charge terminal)

end GibbsRecursion
end
end Erdos539Geometry
