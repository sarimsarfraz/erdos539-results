/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyFibring
import Erdos539.StationaryEntropyReference

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance referenceFibringImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- The same-law coefficient-three reference potential from the notes. -/
def stationaryReferenceDefect (S : Finset G) (ν u : S → ℝ) : ℝ :=
  stationaryEntropyDefect S ν + 3 * finiteRelEntropy ν u

omit [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem stationaryReferenceDefect_nonneg {S : Finset G} {ν u : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (hu : ∀ x, 0 < u x) (hus : ∑ x, u x = 1) :
    0 ≤ stationaryReferenceDefect S ν u := by
  have h₁ := (stationaryEntropyDefect_bounds S ν hν hs).1
  have h₂ := finiteRelEntropy_nonneg ν u hν (fun x ↦ (hu x).le) hs hus (fun x _ ↦ hu x)
  unfold stationaryReferenceDefect
  linarith

/-- Exact conditional reference laws pay their KL penalties in the same
fibring inequality. No endpoint is recomputed in this theorem. -/
theorem stationaryReferenceDefect_superadditive {S : Finset G} {ν u : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (hu : ∀ x, 0 < u x) (φ : G →+ H) :
    stationaryReferenceDefect (S.image φ) (finitePush ν (imageEndpoint S φ)) (finitePush u (imageEndpoint S φ)) +
      (∑ y, finitePush ν (imageEndpoint S φ) y *
        stationaryReferenceDefect (fiber S φ y.val) (imageFiberReference S φ ν y) (imageFiberReference S φ u y)) ≤
      stationaryReferenceDefect S ν u := by
  have h := stationaryEntropyDefect_superadditive hν hs φ
  have he := imageFiber_relativeEntropy_chain S φ ν u hν hu
  unfold stationaryReferenceDefect
  simp only [mul_add, Finset.sum_add_distrib]
  have hsum : (∑ y, finitePush ν (imageEndpoint S φ) y *
      (3 * finiteRelEntropy (imageFiberReference S φ ν y) (imageFiberReference S φ u y))) =
      3 * ∑ y, finitePush ν (imageEndpoint S φ) y *
        finiteRelEntropy (imageFiberReference S φ ν y) (imageFiberReference S φ u y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsum]
  linarith

def stationaryReferenceCutCost (S : Finset G) (φ : G →+ H) (ν u : S → ℝ) : ℝ :=
  stationaryReferenceDefect (S.image φ) (finitePush ν (imageEndpoint S φ)) (finitePush u (imageEndpoint S φ)) +
    ∑ y, finitePush ν (imageEndpoint S φ) y *
      stationaryReferenceDefect (fiber S φ y.val) (imageFiberReference S φ ν y) (imageFiberReference S φ u y)

/-- Both cut costs use the same parent laws. Applied to complementary
coordinate maps, this is the coefficient-two shared reference budget. -/
theorem stationaryReferenceDefect_two_cuts {K : Type*} [AddCommGroup K] [DecidableEq K]
    {S : Finset G} {ν u : S → ℝ} (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1)
    (hu : ∀ x, 0 < u x) (φ : G →+ H) (ψ : G →+ K) :
    stationaryReferenceCutCost S φ ν u + stationaryReferenceCutCost S ψ ν u ≤
      2 * stationaryReferenceDefect S ν u := by
  have h₁ := stationaryReferenceDefect_superadditive hν hs hu φ
  have h₂ := stationaryReferenceDefect_superadditive hν hs hu ψ
  change stationaryReferenceCutCost S φ ν u ≤ _ at h₁
  change stationaryReferenceCutCost S ψ ν u ≤ _ at h₂
  linarith

omit [AddCommGroup H] [DecidableEq H] in
/-- The canonical reference Gibbs endpoint realizes exactly the initial
reference deficit in this same-law potential. -/
theorem stationaryReferenceDefect_referenceEndpoint {S : Finset G} (hS : S.Nonempty)
    {u : S → ℝ} (hu : ∀ x, 0 < u x) :
    stationaryReferenceDefect S (referenceEndpoint S u) u = referenceDeficit S u :=
  (referenceDeficit_eq_stationaryEntropyDefect hS hu).symm

end
end Erdos539Geometry
