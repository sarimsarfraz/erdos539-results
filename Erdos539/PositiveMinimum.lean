/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ConditionalSuperSqrt
import Erdos539.SuperSqrt
import Erdos539.SharpUpper
import Erdos539.IntegerProducts
import Erdos539.IntervalExact
import Mathlib.Data.Nat.Prime.Infinite

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- The manuscript's unrestricted minimum, over positive integers only. -/
def positiveCofactorMinimum (n : ℕ) : ℕ :=
  sInf {q : ℕ | ∃ A : Finset ℕ, A.card = n ∧
    (∀ a ∈ A, 0 < a) ∧ (cofactors A).card = q}

theorem positiveCofactorMinimum_attained (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, 0 < a) ∧
      (cofactors A).card = positiveCofactorMinimum n := by
  apply Nat.sInf_mem (s := {q : ℕ | ∃ A : Finset ℕ, A.card = n ∧
    (∀ a ∈ A, 0 < a) ∧ (cofactors A).card = q})
  let A := (Finset.range n).image Nat.succ
  refine ⟨(cofactors A).card, A, ?_, ?_, rfl⟩
  · simp only [A, Finset.card_image_of_injective _ Nat.succ_injective, Finset.card_range]
  · intro a ha
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp ha
    exact Nat.succ_pos b

theorem positiveCofactorMinimum_le {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    positiveCofactorMinimum A.card ≤ (cofactors A).card :=
  Nat.sInf_le ⟨A, rfl, hA, rfl⟩

/-- A harmless extra zero coordinate ensures the model dimension is positive,
even for sets whose only possible positive integer is one. -/
theorem exists_positive_dimension_integer_model {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    ∃ d : ℕ, 0 < d ∧ ∃ F : Finset (Fin d → ℤ), F.card = A.card ∧
      (integerPositiveDifferences F).card = (cofactors A).card := by
  let ι := ↥(coordinateSupport (exponentSet A)) ⊕ Unit
  let H := integerProduct (integerExponentSet A) (intervalVectors 1)
  let d := Fintype.card ι
  let e : ι ≃ Fin d := Fintype.equivFin ι
  refine ⟨d, ?_, H.image (reindexInteger e), ?_, ?_⟩
  · dsimp only [d, ι]
    simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_unit]
    omega
  · rw [reindexInteger_card]
    dsimp only [H]
    rw [integerProduct_card, intervalVectors_card, mul_one, integerExponentSet_card hA]
  · rw [integerPositiveDifferences_reindex_card]
    dsimp only [H]
    rw [integerProduct_positiveDifferences, integerProduct_card,
      intervalVectors_posDiff_card_eq (by decide : 0 < 1), mul_one,
      integerPositiveDifferences_integerExponentSet_card hA]

theorem exists_distinct_primes (d : ℕ) : ∃ p : Fin d ↪ ℕ, ∀ i, (p i).Prime := by
  have hinf : Set.Infinite {p : ℕ | p.Prime} :=
    fun hf ↦ Nat.not_bddAbove_setOf_prime hf.bddAbove
  let e := hinf.natEmbedding {p : ℕ | p.Prime}
  refine ⟨⟨fun i ↦ (e i.val).val, ?_⟩, fun i ↦ (e i.val).property⟩
  intro i j hij
  exact Fin.ext (e.injective (Subtype.ext hij))

theorem positiveCofactorMinimum_le_fixedDimensionalMinimum {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    positiveCofactorMinimum n ≤ fixedDimensionalMinimum d n := by
  obtain ⟨_C, _hC, hf⟩ := exists_sharp_upper_construction hd
  obtain ⟨F₀, hF₀, _hD₀⟩ := hf n hn
  obtain ⟨F, hF, hD⟩ := fixedDimensionalMinimum_attained ⟨F₀, hF₀⟩
  obtain ⟨p, hp⟩ := exists_distinct_primes d
  obtain ⟨A, hA, hq, hsupport⟩ := exists_prime_realization p hp F
  have h := positiveCofactorMinimum_le (fun a ha ↦ (hsupport a ha).1)
  rwa [hA, hF, hq, hD] at h

/-- The minimum over dimensions is over positive dimensions; dimension zero
would otherwise introduce the default infimum of an empty set of examples. -/
theorem positiveCofactorMinimum_eq_min_dimensions {n : ℕ} (hn : 0 < n) :
    positiveCofactorMinimum n =
      sInf {q : ℕ | ∃ d : ℕ, 0 < d ∧ fixedDimensionalMinimum d n = q} := by
  apply le_antisymm
  · obtain ⟨d, hd, he⟩ := Nat.sInf_mem
      (show {q : ℕ | ∃ d : ℕ, 0 < d ∧ fixedDimensionalMinimum d n = q}.Nonempty from
        ⟨fixedDimensionalMinimum 1 n, 1, by decide, rfl⟩)
    rw [← he]
    exact positiveCofactorMinimum_le_fixedDimensionalMinimum hd hn
  · obtain ⟨A, hA, hpos, hq⟩ := positiveCofactorMinimum_attained n
    obtain ⟨d, hd, F, hF, hD⟩ := exists_positive_dimension_integer_model hpos
    calc
      sInf {q : ℕ | ∃ d : ℕ, 0 < d ∧ fixedDimensionalMinimum d n = q}
          ≤ fixedDimensionalMinimum d n := Nat.sInf_le ⟨d, hd, rfl⟩
      _ ≤ (integerPositiveDifferences F).card := fixedDimensionalMinimum_le F (hF.trans hA)
      _ = _ := hD.trans hq

/-- The zero-inclusive Formal Conjectures minimum is no larger than the
positive-integer minimum from the manuscript. -/
theorem cofactorThreshold_le_positiveCofactorMinimum (n : ℕ) :
    Erdos539.cofactorThreshold n ≤ positiveCofactorMinimum n := by
  obtain ⟨A, hA, _hpos, hq⟩ := positiveCofactorMinimum_attained n
  exact hq ▸ Erdos539.cofactorThreshold_le hA

/-- The manuscript's unrestricted theorem, with the same explicit constant. -/
theorem positiveCofactorMinimum_super_sqrt_explicit :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp ((1 / 16000 : ℝ) *
        Real.sqrt (Real.log n / Real.log (Real.log n))) ≤ (positiveCofactorMinimum n : ℝ) := by
  filter_upwards [Erdos539.cofactorThreshold_super_sqrt_explicit] with n hn
  exact hn.trans (by exact_mod_cast cofactorThreshold_le_positiveCofactorMinimum n)

/-- The proposed joint projection estimate has the same checked implication
for the manuscript's positive-integer minimum. -/
theorem positiveCofactorMinimum_strong_bound_of_joint_projections {A B η : ℝ}
    (hproj : JointProjectionHypothesis A B η) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp (c * Real.sqrt (Real.log n)) ≤ (positiveCofactorMinimum n : ℝ) := by
  obtain ⟨c, hc, he⟩ := Erdos539.cofactorThreshold_strong_bound_of_joint_projections hproj hA hB hη hη1
  refine ⟨c, hc, ?_⟩
  filter_upwards [he] with n hn
  exact hn.trans (by exact_mod_cast cofactorThreshold_le_positiveCofactorMinimum n)

end
end Erdos539Geometry
