/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateSweepStep
import Erdos539.OptimalFiberKernels

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Perform exactly one update for each coordinate in a finite mask.
The coupling retains the original anchor, preserves the original law,
and keeps every unvisited coordinate unchanged on its actual support. -/
theorem exists_stationary_coordinate_sweep {ι α β δ : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (coord : ι → α → δ)
    (q : ι → α → α → β) (hq : CoordinateChannelDepends coord q)
    (K : ι → FiniteMarkovKernel α α) (hK : ∀ i, (K i).Preserves ν)
    (hcoord : ∀ i, CoordinateTransition i coord (K i)) (I : Finset ι) :
    ∃ p ∈ stationaryCouplings ν, SweepSupport I coord p ∧
      finiteEntropy ν + (∑ i ∈ I, ∑ a, ν a * finiteEntropy (finitePush ((K i).weight a) (q i a))) ≤
        finiteEntropy (finitePush p (retainedOutput I q)) := by
  induction I using Finset.induction_on with
  | empty =>
    let p := (identityKernel α).joint ν
    have hp : p ∈ stationaryCouplings ν :=
      ⟨(identityKernel α).joint_nonneg ν hν, (identityKernel α).joint_fst ν, identityKernel_preserves ν⟩
    refine ⟨p, hp, ?_, ?_⟩
    · intro a x hax j _
      have hxa : x = a := by
        by_contra hn
        apply hax
        simp [p, FiniteMarkovKernel.joint, identityKernel, hn]
      rw [hxa]
    · let e : α → α × (ι → Option β) := fun a ↦ (a, fun _ ↦ none)
      have hmap : retainedOutput (∅ : Finset ι) q = e ∘ Prod.fst := by
        funext z
        exact retainedOutput_empty q z
      rw [hmap, ← finitePush_comp, hp.2.1]
      have hH := finiteEntropy_push_eq_of_support_injective ν e
        (fun a b _ _ he ↦ congrArg Prod.fst he)
      simp only [Finset.sum_empty, add_zero, hH, le_refl]
  | @insert i I hi ih =>
    obtain ⟨p, hp, hsupport, hentropy⟩ := ih
    refine ⟨(K i).nextCoupling p, (K i).nextCoupling_stationary ν (hK i) p hp,
      nextCoupling_sweepSupport I i coord p hsupport (K i) (hcoord i), ?_⟩
    have hstep := coordinate_sweep_step_entropy I i hi coord q hq ν p hp hsupport (K i) (hcoord i)
    rw [Finset.sum_insert hi]
    linarith

/-- The full visited output contains exactly the original coordinatewise
channel output, up to an injective Some tag in every coordinate. -/
theorem retainedOutput_univ_entropy {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (p : α × α → ℝ) (q : ι → α → α → β) :
    finiteEntropy (finitePush p (retainedOutput Finset.univ q)) =
      finiteEntropy (finitePush p (fun z ↦ (z.1, fun i ↦ q i z.1 z.2))) := by
  let e : (α × (ι → β)) → α × (ι → Option β) := fun z ↦ (z.1, fun i ↦ some (z.2 i))
  have hmap : retainedOutput Finset.univ q = e ∘ (fun z : α × α ↦ (z.1, fun i ↦ q i z.1 z.2)) := by
    funext z
    apply Prod.ext
    · rfl
    funext i
    simp [retainedOutput, maskedCoordinateOutput, e]
  rw [hmap, ← finitePush_comp]
  apply finiteEntropy_push_eq_of_support_injective
  intro a b _ _ he
  apply Prod.ext
  · have hfirst := congrArg Prod.fst he
    exact hfirst
  funext i
  have h := congrFun (congrArg Prod.snd he) i
  exact Option.some.inj h

theorem couplingOutputEntropy_le_stationaryCapacity {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (p : α × α → ℝ) (hp : p ∈ stationaryCouplings ν) :
    couplingOutputEntropy ν channel p ≤ stationaryCapacity ν channel := by
  obtain ⟨r, hr, hmax⟩ := exists_stationaryCouplingMax ν hν hs channel
  have hg : IsGreatest (couplingOutputEntropy ν channel '' stationaryCouplings ν)
      (couplingOutputEntropy ν channel r) := by
    refine ⟨⟨r, hr, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hmax s hs
  rw [stationaryCapacity, hg.csSup_eq]
  exact hmax p hp

/-- A complete simultaneous sweep lower bound for the actual stationary
capacity. Each coordinate kernel is used once and every intermediate
state has the same law; no independence between coordinates is assumed. -/
theorem stationaryCapacity_coordinate_sweep {ι α β δ : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (coord : ι → α → δ) (q : ι → α → α → β) (hq : CoordinateChannelDepends coord q)
    (K : ι → FiniteMarkovKernel α α) (hK : ∀ i, (K i).Preserves ν)
    (hcoord : ∀ i, CoordinateTransition i coord (K i)) :
    (∑ i, ∑ a, ν a * finiteEntropy (finitePush ((K i).weight a) (q i a))) ≤
      stationaryCapacity ν (fun a x i ↦ q i a x) := by
  obtain ⟨p, hp, _, he⟩ := exists_stationary_coordinate_sweep ν hν coord q hq K hK hcoord Finset.univ
  rw [retainedOutput_univ_entropy] at he
  have hcap := couplingOutputEntropy_le_stationaryCapacity ν hν hs (fun a x i ↦ q i a x) p hp
  unfold couplingOutputEntropy at hcap
  linarith

end
end Erdos539Geometry
