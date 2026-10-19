/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MaskedOutputs

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Coordinates outside the visited mask still equal the original anchor. -/
def SweepSupport {ι α δ : Type*} (I : Finset ι) (coord : ι → α → δ) (p : α × α → ℝ) : Prop :=
  ∀ a y, p (a, y) ≠ 0 → ∀ j, j ∉ I → coord j a = coord j y

/-- A transition changes only its selected coordinate on its nonzero support. -/
def CoordinateTransition {ι α δ : Type*} [Fintype α]
    (i : ι) (coord : ι → α → δ) (k : FiniteMarkovKernel α α) : Prop :=
  ∀ a x, k.weight a x ≠ 0 → ∀ j, j ≠ i → coord j x = coord j a

/-- Output coordinate j depends only on the two endpoint coordinates j. -/
def CoordinateChannelDepends {ι α β δ : Type*}
    (coord : ι → α → δ) (q : ι → α → α → β) : Prop :=
  ∀ j a x a' x', coord j a = coord j a' → coord j x = coord j x' → q j a x = q j a' x'

theorem nextCoupling_sweepSupport {ι α δ : Type*} [Fintype α]
    (I : Finset ι) (i : ι) (coord : ι → α → δ) (p : α × α → ℝ)
    (hp : SweepSupport I coord p) (k : FiniteMarkovKernel α α) (hk : CoordinateTransition i coord k) :
    SweepSupport (insert i I) coord (k.nextCoupling p) := by
  apply k.nextCoupling_support p (fun a x ↦ ∀ j, j ∉ insert i I → coord j a = coord j x)
  intro a y x hpay hkyx j hj
  have hnot : j ≠ i ∧ j ∉ I := by simpa only [Finset.mem_insert, not_or] using hj
  have hjI := hnot.2
  have hji := hnot.1
  exact (hp a y hpay j hjI).trans (hk y x hkyx j hji).symm

/-- Exact entropy gain when updating a coordinate that has not been
visited. Every increment remains an increment from the original anchor. -/
theorem coordinate_sweep_step_entropy {ι α β δ : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (I : Finset ι) (i : ι) (hi : i ∉ I) (coord : ι → α → δ)
    (q : ι → α → α → β) (hq : CoordinateChannelDepends coord q)
    (ν : α → ℝ) (p : α × α → ℝ) (hp : p ∈ stationaryCouplings ν)
    (hsupport : SweepSupport I coord p)
    (k : FiniteMarkovKernel α α) (hk : CoordinateTransition i coord k) :
    finiteEntropy (finitePush p (retainedOutput I q)) +
      (∑ a, ν a * finiteEntropy (finitePush (k.weight a) (q i a))) ≤
      finiteEntropy (finitePush (k.nextCoupling p) (retainedOutput (insert i I) q)) := by
  let g : (α × α) × α → (α × (ι → Option β)) × β :=
    fun z ↦ (retainedOutput I q z.1, q i z.1.2 z.2)
  let r := k.stepJoint p
  let u := finitePush r g
  have hmap : finitePush (k.nextCoupling p) (retainedOutput (insert i I) q) =
      finitePush u (insertMaskedOutput i) := by
    rw [FiniteMarkovKernel.nextCoupling, finitePush_comp, finitePush_comp]
    apply finitePush_congr_on_support
    intro z hz
    have hz' : p z.1 * k.weight z.1.2 z.2 ≠ 0 := hz
    obtain ⟨hpz, hkz⟩ := mul_ne_zero_iff.mp hz'
    apply retainedOutput_insert_step I i q z.1.1 z.1.2 z.2
    · exact hq i _ _ _ _ (hsupport _ _ hpz i hi) rfl
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; exact hi hj
      exact hq j _ _ _ _ rfl (hk _ _ hkz j hji)
  have hinactive (v : (α × (ι → Option β)) × β) (hv : u v ≠ 0) : v.1.2 i = none := by
    by_contra hn
    apply hv
    apply finitePush_eq_zero_of_fiber_zero
    intro z hz
    have he : (g z).1.2 i = none := maskedCoordinateOutput_inactive I q z.1.1 z.1.2 hi
    rw [hz] at he
    exact False.elim (hn he)
  have hH : finiteEntropy (finitePush u (insertMaskedOutput i)) = finiteEntropy u := by
    apply finiteEntropy_push_eq_of_support_injective
    intro v w hv hw he
    exact insertMaskedOutput_injective_on_inactive i v w (hinactive v hv) (hinactive w hw) he
  have h := k.step_output_entropy_increment p hp.1 (retainedOutput I q) (q i)
  rw [hp.2.2] at h
  rw [hmap, hH]
  exact h

end
end Erdos539Geometry
