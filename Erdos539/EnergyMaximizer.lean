/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedEnergyRoot
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def extendWeight (S : Finset G) (f : S → ℝ) (x : G) : ℝ :=
  if h : x ∈ S then f ⟨x, h⟩ else 0

omit [AddCommGroup G] in
@[simp] theorem extendWeight_mem (S : Finset G) (f : S → ℝ) (x : S) :
    extendWeight S f x = f x := by simp [extendWeight]

omit [AddCommGroup G] in
@[fun_prop] theorem continuous_extendWeight_apply (S : Finset G) (x : G) :
    Continuous (fun f : S → ℝ ↦ extendWeight S f x) := by
  by_cases hx : x ∈ S
  · simp only [extendWeight, dif_pos hx]
    fun_prop
  · simp only [extendWeight, dif_neg hx]
    fun_prop

def admissibleWeights (S : Finset G) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x ^ 2 = 1}

omit [AddCommGroup G] [DecidableEq G] in
theorem admissibleWeights_isCompact (S : Finset G) : IsCompact (admissibleWeights S) := by
  have he : admissibleWeights S = Set.Icc (0 : S → ℝ) 1 ∩
      {f : S → ℝ | ∑ x, f x ^ 2 = 1} := by
    ext f
    constructor
    · intro hf
      refine ⟨⟨hf.1, ?_⟩, hf.2⟩
      intro x
      have hs : f x ^ 2 ≤ ∑ y, f y ^ 2 :=
        Finset.single_le_sum (fun y _ ↦ sq_nonneg (f y)) (Finset.mem_univ x)
      rw [hf.2] at hs
      change f x ≤ 1
      nlinarith
    · rintro ⟨⟨hf0, _hf1⟩, hnorm⟩
      exact ⟨hf0, hnorm⟩
  rw [he]
  apply isCompact_Icc.inter_right
  exact isClosed_eq (by fun_prop) continuous_const

omit [AddCommGroup G] [DecidableEq G] in
theorem admissibleWeights_nonempty {S : Finset G} (hS : S.Nonempty) :
    (admissibleWeights S).Nonempty := by
  obtain ⟨a, ha⟩ := hS
  let x : S := ⟨a, ha⟩
  refine ⟨(fun y ↦ if y = x then 1 else 0), ?_, ?_⟩
  · intro y
    dsimp
    split_ifs <;> norm_num
  · simp

omit [AddCommGroup G] in
theorem weightSquareSum_extend (S : Finset G) (f : S → ℝ) :
    weightSquareSum S (extendWeight S f) = ∑ x, f x ^ 2 := by
  unfold weightSquareSum
  rw [← Finset.sum_attach S]
  simp

@[fun_prop] theorem continuous_weightedEnergy_extend (S : Finset G) :
    Continuous (fun f : S → ℝ ↦ weightedEnergy S (extendWeight S f)) := by
  unfold weightedEnergy weightedConvolution
  fun_prop

/-- Exact energy maximizers exist on the finite nonnegative unit sphere. -/
theorem exists_energyMaximizer {S : Finset G} (hS : S.Nonempty) :
    ∃ f ∈ admissibleWeights S, ∀ g ∈ admissibleWeights S,
      weightedEnergy S (extendWeight S g) ≤ weightedEnergy S (extendWeight S f) := by
  exact (admissibleWeights_isCompact S).exists_isMaxOn (admissibleWeights_nonempty hS)
    (continuous_weightedEnergy_extend S).continuousOn

def energyMaximizer (S : Finset G) (hS : S.Nonempty) : S → ℝ :=
  Classical.choose (exists_energyMaximizer hS)

theorem energyMaximizer_spec (S : Finset G) (hS : S.Nonempty) :
    energyMaximizer S hS ∈ admissibleWeights S ∧ ∀ g ∈ admissibleWeights S,
      weightedEnergy S (extendWeight S g) ≤ weightedEnergy S (extendWeight S (energyMaximizer S hS)) :=
  Classical.choose_spec (exists_energyMaximizer hS)

/-- The manuscript's finite weighted energy norm, with the empty-set value zero. -/
def energyNorm (S : Finset G) : ℝ :=
  if hS : S.Nonempty then weightedEnergy S (extendWeight S (energyMaximizer S hS)) else 0

theorem energyNorm_nonneg (S : Finset G) : 0 ≤ energyNorm S := by
  unfold energyNorm
  split_ifs
  · exact weightedEnergy_nonneg _ _
  · exact le_rfl

theorem energyNorm_le_card (S : Finset G) : energyNorm S ≤ S.card := by
  unfold energyNorm
  split_ifs with hS
  · have h := weightedEnergy_le_card_mul_squareSum_sq S (extendWeight S (energyMaximizer S hS))
    rw [weightSquareSum_extend, (energyMaximizer_spec S hS).1.2] at h
    simpa using h
  · exact Nat.cast_nonneg _

theorem energyNorm_ge_admissible {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) : weightedEnergy S (extendWeight S f) ≤ energyNorm S := by
  by_cases hS : S.Nonempty
  · rw [energyNorm, dif_pos hS]
    exact (energyMaximizer_spec S hS).2 f hf
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [admissibleWeights] at hf

end
end Erdos539Geometry
