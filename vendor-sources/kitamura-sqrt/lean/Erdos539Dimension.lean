/-
Copyright 2026 Kenta Kitamura
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Tactic
import PFR.WeakPFR
import Erdos539Factorization
import Erdos539PositiveDiff

/-!
Coordinate projections preserve coordinatewise positive differences.
This file proves the linear-algebraic reduction, without assuming any
small-doubling dimension estimate or any unproved combinatorial bound.
-/

namespace Erdos539Dimension

open Module Submodule

noncomputable section

/-- A finite-dimensional space of real coordinate vectors is separated by
at most its dimension many of the original coordinate functions. -/
theorem exists_coordinate_projection {K ι : Type*} [Field K] [Fintype ι]
    (V : Submodule K (ι → K)) :
    ∃ m : ℕ, m ≤ finrank K V ∧ ∃ c : Fin m → ι,
      Function.Injective (fun v : V => fun j => (v : ι → K) (c j)) := by
  classical
  let e : ι → V →ₗ[K] K := fun i => (LinearMap.proj i).comp V.subtype
  let S := Submodule.span K (Set.range e)
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range e)
  have hdim : finrank K S ≤ finrank K V := by
    calc
      finrank K S ≤ finrank K (Module.Dual K V) := Submodule.finrank_le S
      _ = finrank K V := Subspace.dual_finrank_eq
  choose c hc using hf
  refine ⟨finrank K S, hdim, c, ?_⟩
  intro x y hxy
  apply Subtype.ext
  funext i
  have hz : ∀ j, f j (x - y) = 0 := by
    intro j
    rw [← hc j]
    change (x : ι → K) (c j) - (y : ι → K) (c j) = 0
    exact sub_eq_zero.mpr (congrFun hxy j)
  have he : e i ∈ Submodule.span K (Set.range f) := by
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hall : ∀ z ∈ Submodule.span K (Set.range f), z (x - y) = 0 := by
    intro z hz'
    induction hz' using Submodule.span_induction with
    | mem z hz' =>
        obtain ⟨j, rfl⟩ := hz'
        exact hz j
    | zero => simp
    | add z w _ _ hz hw => simp [hz, hw]
    | smul a z _ hz => simp [hz]
  exact sub_eq_zero.mp (hall (e i) he)

/-- An arbitrary set of coordinate vectors admits an injective coordinate
projection to no more than its affine dimension. -/
theorem exists_coordinate_projection_injOn {K ι : Type*} [Field K] [Fintype ι]
    (A : Set (ι → K)) :
    ∃ m : ℕ, m ≤ finrank K (vectorSpan K A) ∧ ∃ c : Fin m → ι,
      Set.InjOn (fun v : ι → K => fun j => v (c j)) A := by
  obtain ⟨m, hm, c, hc⟩ := exists_coordinate_projection (vectorSpan K A)
  refine ⟨m, hm, c, ?_⟩
  intro x hx y hy hxy
  have hv : x - y ∈ vectorSpan K A := vsub_mem_vectorSpan K hx hy
  have hz : (⟨x - y, hv⟩ : vectorSpan K A) = 0 := by
    apply hc
    funext j
    change x (c j) - y (c j) = 0
    exact sub_eq_zero.mpr (congrFun hxy j)
  have : x - y = 0 := congrArg Subtype.val hz
  exact sub_eq_zero.mp this

#print axioms exists_coordinate_projection
#print axioms exists_coordinate_projection_injOn

/-- The coordinatewise embedding of integral vectors into rational vectors. -/
def intToRat {ι : Type*} : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
  LinearMap.pi fun i => (Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj i)

@[simp] theorem intToRat_apply {ι : Type*} (v : ι → ℤ) (i : ι) :
    intToRat v i = (v i : ℚ) := rfl

theorem intToRat_injective {ι : Type*} : Function.Injective (intToRat (ι := ι)) := by
  intro x y h
  funext i
  have he : (x i : ℚ) = (y i : ℚ) := congrFun h i
  exact_mod_cast he

/-- Passing integral coordinate vectors to rational coordinate vectors preserves
the affine dimension of their integer span. -/
theorem finrank_vectorSpan_intToRat {ι : Type*} [Fintype ι]
    (A : Set (ι → ℤ)) :
    finrank ℚ (vectorSpan ℚ (intToRat '' A)) = finrank ℤ (vectorSpan ℤ A) := by
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hmap : (vectorSpan ℤ A).map intToRat = vectorSpan ℤ (intToRat '' A) :=
    intToRat.toAffineMap.map_vectorSpan
  have hfin : Module.Finite ℤ (vectorSpan ℤ (intToRat '' A)) := by
    rw [← hmap]
    infer_instance
  have : Module.Finite ℤ (Submodule.span ℤ ((intToRat '' A) -ᵥ (intToRat '' A))) := by
    rw [← vectorSpan_def]
    exact hfin
  calc
    finrank ℚ (vectorSpan ℚ (intToRat '' A)) =
        finrank ℤ (vectorSpan ℤ (intToRat '' A)) := by
      simp only [vectorSpan_def]
      exact Submodule.finrank_span_eq_finrank_span ℤ ℚ _
    _ = finrank ℤ (vectorSpan ℤ A) := by
      rw [← hmap]
      exact (Submodule.equivMapOfInjective intToRat intToRat_injective _).finrank_eq.symm

/-- An integral set admits an injective coordinate projection using at most
the dimension of its integer affine span. -/
theorem exists_int_coordinate_projection {ι : Type*} [Fintype ι]
    (A : Set (ι → ℤ)) :
    ∃ m : ℕ, m ≤ finrank ℤ (vectorSpan ℤ A) ∧ ∃ c : Fin m → ι,
      Set.InjOn (fun v : ι → ℤ => fun j => v (c j)) A := by
  obtain ⟨m, hm, c, hc⟩ := exists_coordinate_projection_injOn (intToRat '' A)
  refine ⟨m, by rwa [finrank_vectorSpan_intToRat] at hm, c, ?_⟩
  intro x hx y hy hxy
  apply intToRat_injective
  apply hc (Set.mem_image_of_mem intToRat hx) (Set.mem_image_of_mem intToRat hy)
  funext j
  change (x (c j) : ℚ) = (y (c j) : ℚ)
  exact congrArg Int.cast (congrFun hxy j)

#print axioms finrank_vectorSpan_intToRat
#print axioms exists_int_coordinate_projection

open Erdos539Geometry
open scoped Pointwise

theorem integerDifferences_coe {ι : Type*} (F : Finset (ι → ℤ)) :
    (integerDifferences F : Set (ι → ℤ)) = (F : Set (ι → ℤ)) - F := by
  classical
  ext z
  simp only [integerDifferences, Finset.mem_coe, Finset.mem_image, Prod.exists,
    Finset.mem_product, Set.mem_sub]
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, h⟩
    exact ⟨x, hx, y, hy, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, y, ⟨hx, hy⟩, h⟩

/-- A nonempty integer set with small difference set has a large real-coordinate
image in a dimension depending only on the doubling constant. All mathematical
inputs are proved, including the weak PFR theorem imported above. -/
theorem exists_small_dimension_subset {ι : Type*} [Fintype ι]
    (F : Finset (ι → ℤ)) (hF : F.Nonempty) (K : ℝ)
    (hDiff : ((integerDifferences F).card : ℝ) ≤ K * F.card) :
    ∃ m : ℕ, m ≤ ⌈(40 / Real.log 2) * Real.log K⌉₊ ∧
      ∃ B : Finset (Fin m → ℝ), B.Nonempty ∧
        K ^ (-17 : ℝ) * F.card ≤ B.card ∧
        (posDiff B).card ≤ (integerPositiveDifferences F).card := by
  classical
  let : DecidableEq (ι → ℤ) := Classical.decEq _
  let : DecidableEq (ι → ℝ) := Classical.decEq _
  have hDiffSet : (Nat.card ((F : Set (ι → ℤ)) - (F : Set (ι → ℤ))) : ℝ) ≤
      K * Nat.card (F : Set (ι → ℤ)) := by
    simpa only [← integerDifferences_coe, Nat.card_coe_set_eq,
      Set.ncard_coe_finset] using hDiff
  obtain ⟨S, hSF, hScard, hSdim⟩ := weak_PFR_int hF hDiffSet
  have hfinite : S.Finite := F.finite_toSet.subset hSF
  let T : Finset (ι → ℤ) := hfinite.toFinset
  have hT : (T : Set (ι → ℤ)) = S := hfinite.coe_toFinset
  have hTF : T ⊆ F := by
    intro x hx
    exact hSF (by simpa only [← hT, Finset.mem_coe] using hx)
  have hK : 0 < K := by
    obtain ⟨x, hx⟩ := hF
    have hzero : (0 : ι → ℤ) ∈ integerDifferences F := by
      change (0 : ι → ℤ) ∈ (integerDifferences F : Set (ι → ℤ))
      rw [integerDifferences_coe]
      exact Set.mem_sub.mpr ⟨x, hx, x, hx, sub_self x⟩
    have hcardpos : (0 : ℝ) < (integerDifferences F).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨0, hzero⟩
    have hprodpos := lt_of_lt_of_le hcardpos hDiff
    nlinarith [show (0 : ℝ) ≤ F.card by positivity]
  have hTcard : K ^ (-17 : ℝ) * F.card ≤ T.card := by
    simpa only [← hT, Nat.card_coe_set_eq, Set.ncard_coe_finset] using hScard
  have hTnonempty : T.Nonempty := by
    apply Finset.card_pos.mp
    have hFp : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
    have hTp : (0 : ℝ) < T.card :=
      lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hK _) hFp) hTcard
    exact_mod_cast hTp
  obtain ⟨m, hm, c, hc⟩ := exists_int_coordinate_projection S
  have hmbound : m ≤ ⌈(40 / Real.log 2) * Real.log K⌉₊ := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact (le_trans (by exact_mod_cast hm) hSdim).trans (Nat.le_ceil _)
  let : DecidableEq (Fin m → ℤ) := Classical.decEq _
  let : DecidableEq (Fin m → ℝ) := Classical.decEq _
  let U := T.image (fun x => x ∘ c)
  let B := U.image integerToReal
  have hUcard : U.card = T.card := Finset.card_image_of_injOn (by
    simpa only [hT, Function.comp_def] using hc)
  have hBcard : B.card = T.card := by
    exact (integerToReal_image_card U).trans hUcard
  refine ⟨m, hmbound, B, ?_, ?_, ?_⟩
  · exact (hTnonempty.image _).image _
  · simpa only [hBcard] using hTcard
  · have hB : B = (T.image integerToReal).image (fun x => x ∘ c) := by
      simp only [B, U, Finset.image_image]
      rfl
    rw [hB]
    calc
      (posDiff ((T.image integerToReal).image (fun x => x ∘ c))).card =
          ((posDiff (T.image integerToReal)).image (fun x => x ∘ c)).card := by
        exact congrArg Finset.card (posDiff_image_comp (T.image integerToReal) c)
      _ ≤
          (posDiff (T.image integerToReal)).card := Finset.card_image_le
      _ ≤ (posDiff (F.image integerToReal)).card :=
        Finset.card_le_card (posDiff_mono (Finset.image_subset_image hTF))
      _ = (integerPositiveDifferences F).card :=
        realPositiveDifferences_integerToReal_image_card F

#print axioms exists_small_dimension_subset

end
end Erdos539Dimension
