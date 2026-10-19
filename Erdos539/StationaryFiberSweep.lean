/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateSweep

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- The simultaneous sweep using actual optimal stationary couplings in
each conditioning fiber. All states and transitions refer to one law. -/
theorem stationaryCapacity_fiber_sweep {ι α β δ : Type*} {σ : ι → Type*}
    [Fintype ι] [Fintype α] [Fintype β] [∀ i, Fintype (σ i)]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (coord : ι → α → δ) (q : ι → α → α → β) (hq : CoordinateChannelDepends coord q)
    (f : ∀ i, α → σ i)
    (houtside : ∀ i a x, f i x = f i a → ∀ j, j ≠ i → coord j x = coord j a) :
    (∑ i, ∑ b, finitePush ν (f i) b * stationaryCapacity (conditionalWeight ν (f i) b)
      (fun a x ↦ q i a.val x.val)) ≤ stationaryCapacity ν (fun a x i ↦ q i a x) := by
  have hex := fun i ↦ exists_optimal_fiber_kernel ν hν (f i) (q i)
  choose K hK hsupport hentropy using hex
  have hcoord : ∀ i, CoordinateTransition i coord (K i) := by
    intro i a x hax j hji
    exact houtside i a x (hsupport i a x hax) j hji
  have h := stationaryCapacity_coordinate_sweep ν hν hs coord q hq K hK hcoord
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ hentropy i)
  rw [he] at h
  exact h

end
end Erdos539Geometry
