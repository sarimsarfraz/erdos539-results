/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FinitePushProducts
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

@[fun_prop] theorem continuous_finitePush_apply {α β : Type*} [Fintype α]
    (f : α → β) (b : β) : Continuous (fun p : α → ℝ ↦ finitePush p f b) := by
  unfold finitePush
  apply continuous_finset_sum
  intro a _
  by_cases h : f a = b
  · simp only [if_pos h]
    fun_prop
  · simp only [if_neg h]
    fun_prop

@[fun_prop] theorem continuous_finiteEntropy {α : Type*} [Fintype α] :
    Continuous (finiteEntropy (α := α)) := by
  unfold finiteEntropy
  fun_prop

/-- All nonnegative finite couplings with two prescribed equal marginals. -/
def stationaryCouplings {α : Type*} [Fintype α] (ν : α → ℝ) : Set (α × α → ℝ) :=
  {p | (∀ z, 0 ≤ p z) ∧ finitePush p Prod.fst = ν ∧ finitePush p Prod.snd = ν}

theorem stationaryCouplings_nonempty {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) : (stationaryCouplings ν).Nonempty := by
  let p : α × α → ℝ := fun z ↦ if z.1 = z.2 then ν z.1 else 0
  refine ⟨p, ?_, ?_, ?_⟩
  · intro z
    dsimp [p]
    split_ifs
    · exact hν z.1
    · rfl
  · funext a
    rw [finitePush_fst]
    simp [p]
  · funext a
    rw [finitePush_snd]
    simp [p]

theorem stationaryCouplings_isCompact {α : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    IsCompact (stationaryCouplings ν) := by
  have he : stationaryCouplings ν = Set.Icc (0 : α × α → ℝ) 1 ∩
      {p | finitePush p Prod.fst = ν} ∩ {p | finitePush p Prod.snd = ν} := by
    ext p
    constructor
    · rintro ⟨hp, hfirst, hsecond⟩
      refine ⟨⟨⟨hp, ?_⟩, hfirst⟩, hsecond⟩
      intro z
      have hle := le_finitePush p Prod.fst hp z
      rw [hfirst] at hle
      have hνle : ν z.1 ≤ 1 := by
        rw [← hs]
        exact Finset.single_le_sum (fun a _ ↦ hν a) (Finset.mem_univ z.1)
      exact hle.trans hνle
    · rintro ⟨⟨⟨hp, _⟩, hfirst⟩, hsecond⟩
      exact ⟨hp, hfirst, hsecond⟩
  rw [he]
  apply IsCompact.inter_right
  · apply isCompact_Icc.inter_right
    exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const

/-- Conditional output entropy of a finite stationary coupling. The
first endpoint is retained as part of the output, so conditioning is literal. -/
def couplingOutputEntropy {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (channel : α → α → β) (p : α × α → ℝ) : ℝ :=
  finiteEntropy (finitePush p (fun z ↦ (z.1, channel z.1 z.2))) - finiteEntropy ν

@[fun_prop] theorem continuous_couplingOutputEntropy {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (channel : α → α → β) : Continuous (couplingOutputEntropy ν channel) := by
  unfold couplingOutputEntropy
  fun_prop

/-- The finite stationary entropy optimization has an exact maximizer,
including laws with zero atoms. No duality premise is assumed. -/
theorem exists_stationaryCouplingMax {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (channel : α → α → β) :
    ∃ p ∈ stationaryCouplings ν, ∀ q ∈ stationaryCouplings ν,
      couplingOutputEntropy ν channel q ≤ couplingOutputEntropy ν channel p := by
  exact (stationaryCouplings_isCompact ν hν hs).exists_isMaxOn
    (stationaryCouplings_nonempty ν hν) (continuous_couplingOutputEntropy ν channel).continuousOn

/-- The actual maximal conditional output entropy over stationary couplings. -/
def stationaryCapacity {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (channel : α → α → β) : ℝ :=
  sSup (couplingOutputEntropy ν channel '' stationaryCouplings ν)

theorem stationaryCapacity_attained {α β : Type*} [Fintype α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (channel : α → α → β) :
    ∃ p ∈ stationaryCouplings ν, couplingOutputEntropy ν channel p = stationaryCapacity ν channel := by
  obtain ⟨p, hp, hmax⟩ := exists_stationaryCouplingMax ν hν hs channel
  refine ⟨p, hp, ?_⟩
  have hg : IsGreatest (couplingOutputEntropy ν channel '' stationaryCouplings ν)
      (couplingOutputEntropy ν channel p) := by
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hmax q hq
  exact hg.csSup_eq.symm

end
end Erdos539Geometry
