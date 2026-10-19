/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteKernelEntropy
import Erdos539.FiniteCouplings

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

namespace FiniteMarkovKernel
variable {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]

def precompose (k : FiniteMarkovKernel β γ) (f : α → β) : FiniteMarkovKernel α γ where
  weight a := k.weight (f a)
  nonneg a := k.nonneg (f a)
  sum_one a := k.sum_one (f a)

/-- Keep the original anchor and update the current endpoint once. -/
def stepJoint (k : FiniteMarkovKernel β γ) (p : α × β → ℝ) : (α × β) × γ → ℝ :=
  (k.precompose Prod.snd).joint p

def nextCoupling (k : FiniteMarkovKernel β γ) (p : α × β → ℝ) : α × γ → ℝ :=
  finitePush (k.stepJoint p) (fun z ↦ (z.1.1, z.2))

theorem stepJoint_fst (k : FiniteMarkovKernel β γ) (p : α × β → ℝ) :
    finitePush (k.stepJoint p) Prod.fst = p := (k.precompose Prod.snd).joint_fst p

theorem nextCoupling_nonneg (k : FiniteMarkovKernel β γ) (p : α × β → ℝ)
    (hp : ∀ z, 0 ≤ p z) : ∀ z, 0 ≤ k.nextCoupling p z :=
  finitePush_nonneg _ _ ((k.precompose Prod.snd).joint_nonneg p hp)

theorem nextCoupling_fst (k : FiniteMarkovKernel β γ) (p : α × β → ℝ) :
    finitePush (k.nextCoupling p) Prod.fst = finitePush p Prod.fst := by
  rw [nextCoupling, finitePush_comp]
  change finitePush (k.stepJoint p) (Prod.fst ∘ Prod.fst) = _
  rw [← finitePush_comp, k.stepJoint_fst]

theorem nextCoupling_snd (k : FiniteMarkovKernel β γ) (p : α × β → ℝ) :
    finitePush (k.nextCoupling p) Prod.snd = finitePush (k.joint (finitePush p Prod.snd)) Prod.snd := by
  rw [nextCoupling, finitePush_comp]
  funext c
  change finitePush (k.stepJoint p) Prod.snd c =
    finitePush (k.joint (finitePush p Prod.snd)) Prod.snd c
  rw [finitePush_snd, finitePush_snd]
  simp only [stepJoint, precompose, joint, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul, finitePush_snd]

theorem nextCoupling_stationary (k : FiniteMarkovKernel α α) (ν : α → ℝ)
    (hk : k.Preserves ν) (p : α × α → ℝ) (hp : p ∈ stationaryCouplings ν) :
    k.nextCoupling p ∈ stationaryCouplings ν := by
  refine ⟨k.nextCoupling_nonneg p hp.1, ?_, ?_⟩
  · rw [nextCoupling_fst, hp.2.1]
  · rw [nextCoupling_snd, hp.2.2]
    exact hk

/-- One Markov update increases the entropy of retained old outputs by
at least the current-law average of its new conditional output entropy. -/
theorem step_output_entropy_increment (k : FiniteMarkovKernel β γ)
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z)
    (old : α × β → δ) (output : β → γ → ε) :
    finiteEntropy (finitePush p old) +
      (∑ b, finitePush p Prod.snd b * finiteEntropy (finitePush (k.weight b) (output b))) ≤
      finiteEntropy (finitePush (k.stepJoint p) (fun z ↦ (old z.1, output z.1.2 z.2))) := by
  let l := (k.precompose (Prod.snd : α × β → β)).mapOutput (fun z c ↦ output z.2 c)
  have h := l.output_entropy_increment p hp old
  have hmean := finitePush_expectation p Prod.snd
    (fun b ↦ finiteEntropy (finitePush (k.weight b) (output b)))
  change (∑ b, finitePush p Prod.snd b * finiteEntropy (finitePush (k.weight b) (output b))) =
    ∑ z, p z * finiteEntropy (l.weight z) at hmean
  rw [← hmean] at h
  have hj : l.joint p = finitePush (k.stepJoint p) (fun z ↦ (z.1, output z.1.2 z.2)) :=
    ((k.precompose Prod.snd).joint_mapOutput p (fun z c ↦ output z.2 c)).symm
  rw [hj, finitePush_comp] at h
  exact h

/-- Any relation forced by the original support and every nonzero
transition also holds on the next actual coupling's support. -/
theorem nextCoupling_support (k : FiniteMarkovKernel β γ) (p : α × β → ℝ)
    (R : α → γ → Prop)
    (hR : ∀ a b c, p (a, b) ≠ 0 → k.weight b c ≠ 0 → R a c) :
    ∀ a c, k.nextCoupling p (a, c) ≠ 0 → R a c := by
  intro a c hne
  by_contra hn
  apply hne
  apply finitePush_eq_zero_of_fiber_zero
  intro z hz
  obtain ⟨⟨a', b⟩, c'⟩ := z
  have ha : a' = a := congrArg Prod.fst hz
  have hc : c' = c := congrArg Prod.snd hz
  subst a'
  subst c'
  change p (a, b) * k.weight b c = 0
  by_cases hp : p (a, b) = 0
  · simp [hp]
  · by_cases hk : k.weight b c = 0
    · simp [hk]
    · exact False.elim (hn (hR a b c hp hk))

end FiniteMarkovKernel
end
end Erdos539Geometry
