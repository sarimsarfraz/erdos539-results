/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryReferenceFibring
import Erdos539.GibbsReferenceState

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A fixed nonnegative probability law and a positive reference on the same
actual support. Positive-mass descendants carry their literal conditionals. -/
structure StationaryReferenceState (G : Type*) where
  support : Finset G
  nonempty : support.Nonempty
  law : support → ℝ
  law_nonneg : ∀ x, 0 ≤ law x
  law_sum : ∑ x, law x = 1
  reference : support → ℝ
  reference_pos : ∀ x, 0 < reference x
  reference_sum : ∑ x, reference x = 1

namespace StationaryReferenceState
local instance stationaryStateImageDecidableEq (s : StationaryReferenceState G) (φ : G →+ G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

def cost (s : StationaryReferenceState G) : ℝ := stationaryReferenceDefect s.support s.law s.reference

omit [DecidableEq G] in
theorem cost_nonneg (s : StationaryReferenceState G) : 0 ≤ s.cost :=
  stationaryReferenceDefect_nonneg s.law_nonneg s.law_sum s.reference_pos s.reference_sum

def image (s : StationaryReferenceState G) (φ : G →+ G) : StationaryReferenceState G where
  support := s.support.image φ
  nonempty := s.nonempty.image φ
  law := finitePush s.law (imageEndpoint s.support φ)
  law_nonneg := finitePush_nonneg s.law (imageEndpoint s.support φ) s.law_nonneg
  law_sum := by rw [finitePush_sum, s.law_sum]
  reference := finitePush s.reference (imageEndpoint s.support φ)
  reference_pos := finitePush_imageEndpoint_pos s.support φ s.reference s.reference_pos
  reference_sum := by rw [finitePush_sum, s.reference_sum]

/-- All fibers are averaged with the current conditional original law. -/
def sample (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ) : ℝ :=
  finitePush s.law (imageEndpoint s.support φ) y

theorem sample_nonneg (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ) : 0 ≤ s.sample φ y :=
  finitePush_nonneg s.law (imageEndpoint s.support φ) s.law_nonneg y

theorem sample_sum (s : StationaryReferenceState G) (φ : G →+ G) : ∑ y, s.sample φ y = 1 := by
  unfold sample
  rw [finitePush_sum, s.law_sum]

/-- The conditional endpoint on a positive-mass fiber. On a zero-mass
fiber use the conditional reference, which has no effect on weighted costs. -/
def fiberLaw (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ) :
    Erdos539Geometry.fiber s.support φ y.val → ℝ :=
  if s.sample φ y = 0 then imageFiberReference s.support φ s.reference y
  else imageFiberReference s.support φ s.law y

theorem fiberLaw_nonneg (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ)
    (x : Erdos539Geometry.fiber s.support φ y.val) : 0 ≤ s.fiberLaw φ y x := by
  unfold fiberLaw
  split_ifs
  · exact (imageFiberReference_pos s.support φ s.reference s.reference_pos y x).le
  · exact imageFiberReference_nonneg s.support φ s.law s.law_nonneg y x

theorem fiberLaw_sum (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ) :
    ∑ x, s.fiberLaw φ y x = 1 := by
  unfold fiberLaw
  split_ifs with h
  · exact imageFiberReference_sum s.support φ s.reference s.reference_pos y
  · exact imageFiberReference_sum_of_mass_ne_zero s.support φ s.law y h

def fiber (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ) : StationaryReferenceState G where
  support := Erdos539Geometry.fiber s.support φ y.val
  nonempty := imageFiber_nonempty s.support φ y
  law := s.fiberLaw φ y
  law_nonneg := s.fiberLaw_nonneg φ y
  law_sum := s.fiberLaw_sum φ y
  reference := imageFiberReference s.support φ s.reference y
  reference_pos := imageFiberReference_pos s.support φ s.reference s.reference_pos y
  reference_sum := imageFiberReference_sum s.support φ s.reference s.reference_pos y

theorem fiber_law_reconstruct (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ)
    (x : (s.fiber φ y).support) : s.sample φ y * (s.fiber φ y).law x =
      s.law (imageFiberEndpoint s.support φ y x) := by
  have h := imageFiberReference_reconstruct_of_nonneg s.support φ s.law s.law_nonneg y x
  change s.sample φ y * imageFiberReference s.support φ s.law y x = _ at h
  change s.sample φ y * s.fiberLaw φ y x = _
  by_cases hy : s.sample φ y = 0
  · simpa only [hy, zero_mul] using h
  · simpa only [fiberLaw, if_neg hy] using h

theorem fiber_law_eq_conditional (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ)
    (hy : s.sample φ y ≠ 0) : (s.fiber φ y).law = imageFiberReference s.support φ s.law y := by
  exact if_neg hy

theorem fiber_cost_weighted (s : StationaryReferenceState G) (φ : G →+ G) (y : s.support.image φ) :
    s.sample φ y * (s.fiber φ y).cost = s.sample φ y *
      stationaryReferenceDefect (Erdos539Geometry.fiber s.support φ y.val)
        (imageFiberReference s.support φ s.law y) (imageFiberReference s.support φ s.reference y) := by
  by_cases hy : s.sample φ y = 0
  · simp only [hy, zero_mul]
  · simp only [cost, fiber, fiberLaw, if_neg hy]

theorem cost_fibring (s : StationaryReferenceState G) (φ : G →+ G) :
    (s.image φ).cost + (∑ y, s.sample φ y * (s.fiber φ y).cost) ≤ s.cost := by
  simp_rw [fiber_cost_weighted]
  exact stationaryReferenceDefect_superadditive s.law_nonneg s.law_sum s.reference_pos φ

theorem cost_two_cuts (s : StationaryReferenceState G) (φ ψ : G →+ G) :
    (s.image φ).cost + (s.image ψ).cost +
      (∑ y, s.sample φ y * (s.fiber φ y).cost) + (∑ z, s.sample ψ z * (s.fiber ψ z).cost) ≤ 2 * s.cost := by
  have hφ := s.cost_fibring φ
  have hψ := s.cost_fibring ψ
  linarith

/-- Start from the explicit Gibbs endpoint associated to a carried
reference; future descendants keep its actual conditional laws. -/
def gibbsRoot (s : GibbsReference G) : StationaryReferenceState G where
  support := s.support
  nonempty := s.nonempty
  law := referenceEndpoint s.support s.weight
  law_nonneg := fun x ↦ (referenceEndpoint_pos s.nonempty s.positive x).le
  law_sum := referenceEndpoint_sum s.nonempty s.positive
  reference := s.weight
  reference_pos := s.positive
  reference_sum := s.normalized

theorem gibbsRoot_cost (s : GibbsReference G) : (gibbsRoot s).cost = s.deficit :=
  stationaryReferenceDefect_referenceEndpoint s.nonempty s.positive

end StationaryReferenceState
end
end Erdos539Geometry
