/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryFiberSweep
import Erdos539.StationaryOutputTransport
import Erdos539.StationaryFanCapacity
import Erdos539.StationaryCoordinateEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance stationaryCoordinateSweepDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance stationaryCoordinateProjectionDecidableEq (S : Finset (ι → ℝ)) (I : Finset ι) :
    DecidableEq (projection S I) := Classical.decEq _

/-- One finite alphabet containing all scalar coordinates of all actual
positive differences. Unused labels do not alter channel entropy. -/
def scalarOutputAlphabet (S : Finset (ι → ℝ)) : Finset ℝ :=
  Finset.univ.biUnion (fun i ↦ (posDiff S).image (fun z ↦ z i))

def coordinateOutputLift (S : Finset (ι → ℝ)) (z : posDiff S) (i : ι) : scalarOutputAlphabet S :=
  ⟨z.val i, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩⟩⟩

def scalarCoordinateChannel (S : Finset (ι → ℝ)) (i : ι) (a x : S) : scalarOutputAlphabet S :=
  coordinateOutputLift S (positiveDifferenceChannel S a x) i

theorem coordinateOutputLift_injective (S : Finset (ι → ℝ)) : Function.Injective (coordinateOutputLift S) := by
  intro v w he
  apply Subtype.ext
  funext i
  have h := congrArg Subtype.val (congrFun he i)
  exact h

theorem scalarCoordinateChannel_depends (S : Finset (ι → ℝ)) :
    CoordinateChannelDepends (fun i (x : S) ↦ x.val i) (scalarCoordinateChannel S) := by
  intro i a x a' x' ha hx
  change a.val i = a'.val i at ha
  change x.val i = x'.val i at hx
  apply Subtype.ext
  change max (x.val i - a.val i) 0 = max (x'.val i - a'.val i) 0
  rw [ha, hx]

theorem stationaryCapacity_coordinateChannel_eq (S : Finset (ι → ℝ)) (ν : S → ℝ) :
    stationaryCapacity ν (fun a x i ↦ scalarCoordinateChannel S i a x) = stationaryFanCapacity S ν :=
  stationaryCapacity_map_injective ν (positiveDifferenceChannel S) (coordinateOutputLift S)
    (coordinateOutputLift_injective S)

/-- The actual outside-coordinate projection, retaining its finite image. -/
def outsideEndpoint (S : Finset (ι → ℝ)) (i : ι) : S → projection S (Finset.univ.erase i) :=
  projectEndpoint S (Finset.univ.erase i)

theorem outsideEndpoint_eq_coord (S : Finset (ι → ℝ)) (i : ι) (a x : S)
    (h : outsideEndpoint S i a = outsideEndpoint S i x) (j : ι) (hj : j ≠ i) : a.val j = x.val j := by
  have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
  have he := congrArg (fun v : projection S (Finset.univ.erase i) ↦ v.val ⟨j, hmem⟩) h
  exact he

/-- The scalar coordinate is injective on every actual outside fiber. -/
theorem outsideFiber_coordinate_injective (S : Finset (ι → ℝ)) (i : ι)
    (b : projection S (Finset.univ.erase i)) :
    Function.Injective (fun a : {a : S // outsideEndpoint S i a = b} ↦ a.val.val i) := by
  intro a x he
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    exact he
  · exact outsideEndpoint_eq_coord S i a.val x.val (a.property.trans x.property.symm) j hj

/-- The actual simultaneous stationary sweep on a finite set of real
vectors. Each summand is the capacity of its original outside-coordinate
fiber, with the literal scalar positive increment on that fiber. -/
theorem stationaryFanCapacity_fiber_sweep (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    (∑ i : ι, ∑ b : projection S (Finset.univ.erase i), finitePush ν (outsideEndpoint S i) b *
      stationaryCapacity (conditionalWeight ν (outsideEndpoint S i) b)
        (fun (a x : {a : S // outsideEndpoint S i a = b}) ↦ scalarCoordinateChannel S i a.val x.val)) ≤ stationaryFanCapacity S ν := by
  have h := stationaryCapacity_fiber_sweep (ι := ι) (α := S) (β := scalarOutputAlphabet S) (δ := ℝ) (σ := fun i ↦ projection S (Finset.univ.erase i)) ν hν hs (fun i (x : S) ↦ x.val i)
    (scalarCoordinateChannel S) (scalarCoordinateChannel_depends S) (outsideEndpoint S)
    (fun i a x he j hj ↦ outsideEndpoint_eq_coord S i x a he j hj)
  exact h.trans_eq (stationaryCapacity_coordinateChannel_eq S ν)

end
end Erdos539Geometry
