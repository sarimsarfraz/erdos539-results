/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryCoordinateSweep
import Erdos539.ScalarStationaryBounds

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance stationarySweepLinearDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance stationarySweepLinearProjectionDecidableEq (S : Finset (ι → ℝ)) (I : Finset ι) :
    DecidableEq (projection S I) := Classical.decEq _

/-- Actual conditional entropy of coordinate i given all other coordinates.
The outside fiber is injectively parametrized by its scalar coordinate. -/
def coordinateConditionalEntropy (S : Finset (ι → ℝ)) (ν : S → ℝ) (i : ι) : ℝ :=
  finiteEntropy ν - finiteEntropy (finitePush ν (outsideEndpoint S i))

def coordinateFiberCapacity (S : Finset (ι → ℝ)) (ν : S → ℝ) (i : ι) : ℝ :=
  ∑ b, finitePush ν (outsideEndpoint S i) b *
    stationaryCapacity (conditionalWeight ν (outsideEndpoint S i) b)
      (fun a x ↦ scalarCoordinateChannel S i a.val x.val)

theorem coordinateConditionalEntropy_eq_fiber_average (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (i : ι) :
    coordinateConditionalEntropy S ν i = ∑ b, finitePush ν (outsideEndpoint S i) b *
      finiteEntropy (conditionalWeight ν (outsideEndpoint S i) b) := by
  have h := finiteEntropy_fiber_chain ν hν (outsideEndpoint S i)
  unfold coordinateConditionalEntropy
  linarith

theorem coordinateConditionalEntropy_nonneg (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (i : ι) : 0 ≤ coordinateConditionalEntropy S ν i :=
  sub_nonneg.mpr (finiteEntropy_push_le ν (outsideEndpoint S i) hν)

/-- Both scalar bounds hold in each positive-mass actual outside fiber.
The order is pulled back from its injective original scalar coordinate. -/
theorem outsideFiber_scalar_bounds (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (i : ι) (b : projection S (Finset.univ.erase i))
    (hb : finitePush ν (outsideEndpoint S i) b ≠ 0) :
    let η := conditionalWeight ν (outsideEndpoint S i) b
    let c := fun a x ↦ scalarCoordinateChannel S i a.val x.val
    finiteEntropy η - 2 * Real.log (finiteEntropy η + 2) - 3 ≤ stationaryCapacity η c ∧
      (2 / 3 : ℝ) * finiteEntropy η - scalarStationaryConstant ≤ stationaryCapacity η c := by
  let A := {a : S // outsideEndpoint S i a = b}
  let orderA : LinearOrder A := LinearOrder.lift' (fun a : A ↦ a.val.val i)
    (outsideFiber_coordinate_injective S i b)
  letI : LinearOrder A := orderA
  letI : Preorder A := orderA.toPartialOrder.toPreorder
  let η := conditionalWeight ν (outsideEndpoint S i) b
  let c : A → A → scalarOutputAlphabet S := fun a x ↦ scalarCoordinateChannel S i a.val x.val
  have hη : ∀ a, 0 ≤ η a := conditionalWeight_nonneg ν hν (outsideEndpoint S i) b
  have hsum : ∑ a, η a = 1 := conditionalWeight_sum ν (outsideEndpoint S i) b hb
  have hc : UpperConeInjective c := by
    intro a x y hax hay he
    change a.val.val i ≤ x.val.val i at hax
    change a.val.val i ≤ y.val.val i at hay
    have hv := congrArg Subtype.val he
    change max (x.val.val i - a.val.val i) 0 = max (y.val.val i - a.val.val i) 0 at hv
    rw [max_eq_left (sub_nonneg.mpr hax), max_eq_left (sub_nonneg.mpr hay)] at hv
    apply outsideFiber_coordinate_injective S i b
    linarith
  exact ⟨scalar_stationary_log_bound η hη hsum c hc, scalar_stationary_linear_bound η hη hsum c hc⟩

theorem coordinateFiberCapacity_linear_lower (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (i : ι) :
    (2 / 3 : ℝ) * coordinateConditionalEntropy S ν i - scalarStationaryConstant ≤ coordinateFiberCapacity S ν i := by
  let f := outsideEndpoint S i
  have hmass : ∑ b, finitePush ν f b = 1 := by rw [finitePush_sum, hs]
  have hpoint (b : projection S (Finset.univ.erase i)) :
      finitePush ν f b * ((2 / 3 : ℝ) * finiteEntropy (conditionalWeight ν f b) - scalarStationaryConstant) ≤
      finitePush ν f b * stationaryCapacity (conditionalWeight ν f b)
        (fun a x ↦ scalarCoordinateChannel S i a.val x.val) := by
    by_cases hb : finitePush ν f b = 0
    · simp [hb]
    · exact mul_le_mul_of_nonneg_left (outsideFiber_scalar_bounds S ν hν i b hb).2
        (finitePush_nonneg ν f hν b)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ hpoint b)
  have halg (b : projection S (Finset.univ.erase i)) :
      finitePush ν f b * ((2 / 3 : ℝ) * finiteEntropy (conditionalWeight ν f b) - scalarStationaryConstant) =
        (2 / 3 : ℝ) * (finitePush ν f b * finiteEntropy (conditionalWeight ν f b)) -
          finitePush ν f b * scalarStationaryConstant := by ring
  simp only [halg, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hmass, one_mul] at h
  rw [coordinateConditionalEntropy_eq_fiber_average S ν hν i]
  exact h

/-- The linear simultaneous-sweep entropy bound with the exact manuscript
constant C0 = 1 + (2/3) log 24. All fibers use the same original law. -/
theorem stationary_sweep_linear_bound (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    (∑ i, coordinateConditionalEntropy S ν i) ≤
      (3 / 2 : ℝ) * stationaryFanCapacity S ν +
        (3 / 2 : ℝ) * scalarStationaryConstant * (Fintype.card ι : ℝ) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ ↦ coordinateFiberCapacity_linear_lower S ν hν hs i)
  have hcap := stationaryFanCapacity_fiber_sweep S ν hν hs
  change (∑ i, coordinateFiberCapacity S ν i) ≤ stationaryFanCapacity S ν at hcap
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  linarith

end
end Erdos539Geometry
