/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarStationaryBounds

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- All literal positive-part differences on a finite scalar support. -/
def scalarPositiveDifferences (S : Finset ℝ) : Finset ℝ :=
  (S ×ˢ S).image (fun z ↦ max (z.2 - z.1) 0)

def scalarPositiveDifferenceChannel (S : Finset ℝ) (a x : S) : scalarPositiveDifferences S :=
  ⟨max (x.val - a.val) 0, Finset.mem_image.mpr
    ⟨(a.val, x.val), Finset.mem_product.mpr ⟨a.property, x.property⟩, rfl⟩⟩

theorem scalarPositiveDifferenceChannel_upperConeInjective (S : Finset ℝ) :
    UpperConeInjective (scalarPositiveDifferenceChannel S) := by
  intro a x y hax hay he
  change a.val ≤ x.val at hax
  change a.val ≤ y.val at hay
  have hv := congrArg Subtype.val he
  change max (x.val - a.val) 0 = max (y.val - a.val) 0 at hv
  rw [max_eq_left (sub_nonneg.mpr hax), max_eq_left (sub_nonneg.mpr hay)] at hv
  apply Subtype.ext
  linarith

/-- The scalar stationary fan of the original finite-support law. -/
def scalarStationaryFanCapacity (S : Finset ℝ) (ν : S → ℝ) : ℝ :=
  stationaryCapacity ν (scalarPositiveDifferenceChannel S)

/-- Both explicit bounds in the manuscript's scalar stationary-fan lemma,
for the literal positive-part difference channel. -/
theorem scalarStationaryFanCapacity_lower_bounds (S : Finset ℝ) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    finiteEntropy ν - 2 * Real.log (finiteEntropy ν + 2) - 3 ≤ scalarStationaryFanCapacity S ν ∧
      (2 / 3 : ℝ) * finiteEntropy ν - (1 + (2 / 3 : ℝ) * Real.log 24) ≤ scalarStationaryFanCapacity S ν :=
  ⟨scalar_stationary_log_bound ν hν hs _ (scalarPositiveDifferenceChannel_upperConeInjective S),
    scalar_stationary_linear_bound ν hν hs _ (scalarPositiveDifferenceChannel_upperConeInjective S)⟩

end
end Erdos539Geometry
