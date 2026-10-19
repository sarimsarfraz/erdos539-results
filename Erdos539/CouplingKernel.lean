/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteKernelEntropy
import Erdos539.FiniteEntropyConcavity

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Turn an actual coupling into a stochastic transition. A zero-mass
input uses the identity row; its joint mass remains exactly zero. -/
def couplingKernel {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (p : α × α → ℝ) (hp : p ∈ rowCouplings ν) :
    FiniteMarkovKernel α α where
  weight a x := if ν a = 0 then if x = a then 1 else 0 else p (a, x) / ν a
  nonneg a x := by
    split_ifs
    · exact zero_le_one
    · rfl
    · exact div_nonneg (hp.1 _) (hν a)
  sum_one a := by
    by_cases ha : ν a = 0
    · simp [ha]
    · simp only [if_neg ha, div_eq_mul_inv, ← Finset.sum_mul]
      have hrow := congrFun hp.2 a
      rw [finitePush_fst] at hrow
      rw [hrow, mul_inv_cancel₀ ha]

theorem couplingKernel_joint {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (p : α × α → ℝ) (hp : p ∈ rowCouplings ν) :
    (couplingKernel ν hν p hp).joint ν = p := by
  funext z
  by_cases hz : ν z.1 = 0
  · have hle := le_finitePush p Prod.fst hp.1 z
    rw [hp.2, hz] at hle
    have hpz := le_antisymm hle (hp.1 z)
    simp [FiniteMarkovKernel.joint, couplingKernel, hz, hpz]
  · simp only [FiniteMarkovKernel.joint, couplingKernel, if_neg hz]
    field_simp

theorem couplingKernel_preserves {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (p : α × α → ℝ) (hp : p ∈ stationaryCouplings ν) :
    (couplingKernel ν hν p (stationaryCouplings_subset_rowCouplings ν hp)).Preserves ν := by
  unfold FiniteMarkovKernel.Preserves
  rw [couplingKernel_joint]
  exact hp.2.2

/-- The actual conditional channel entropy of a coupling is its kernel
row average, with the zero-input convention contributing zero. -/
theorem couplingOutputEntropy_eq_kernel_average {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (p : α × α → ℝ) (hp : p ∈ rowCouplings ν)
    (channel : α → α → β) :
    couplingOutputEntropy ν channel p =
      ∑ a, ν a * finiteEntropy (((couplingKernel ν hν p hp).mapOutput channel).weight a) := by
  let k := couplingKernel ν hν p hp
  have hj : k.joint ν = p := couplingKernel_joint ν hν p hp
  unfold couplingOutputEntropy
  conv_lhs => rw [← hj]
  rw [k.joint_mapOutput ν channel, (k.mapOutput channel).joint_entropy ν]
  ring

end
end Erdos539Geometry
