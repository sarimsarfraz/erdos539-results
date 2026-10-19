/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PrimeEncoding

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

def integerShiftToNat (b : ℤ) (x : ι → ℤ) : ι → ℕ := fun i ↦ (x i + b).toNat

def shiftedNatSet (F : Finset (ι → ℤ)) (b : ℤ) : Finset (ι → ℕ) :=
  F.image (integerShiftToNat b)

def natVectorToInt (x : ι → ℕ) : ι → ℤ := fun i ↦ x i

omit [Fintype ι] in
theorem natVectorToInt_injective : Function.Injective (natVectorToInt (ι := ι)) := by
  intro x y h
  funext i
  have hi : (x i : ℤ) = y i := congrFun h i
  exact_mod_cast hi

/-- A finite integer-vector set admits a common nonnegative translation. -/
theorem exists_nonnegative_shift (F : Finset (ι → ℤ)) :
    ∃ b : ℤ, ∀ x ∈ F, ∀ i, 0 ≤ x i + b := by
  classical
  let B : Finset ℕ := (F ×ˢ (Finset.univ : Finset ι)).image (fun p ↦ (p.1 p.2).natAbs)
  refine ⟨((B.sup id : ℕ) : ℤ), ?_⟩
  intro x hx i
  have hm : (x i).natAbs ∈ B := Finset.mem_image.mpr
    ⟨(x, i), Finset.mem_product.mpr ⟨hx, Finset.mem_univ i⟩, rfl⟩
  have h := Finset.le_sup (f := id) hm
  have hi : ((x i).natAbs : ℤ) ≤ ((B.sup id : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hi
  have hlo := neg_abs_le (x i)
  omega

theorem shiftedNatSet_card {F : Finset (ι → ℤ)} {b : ℤ}
    (hb : ∀ x ∈ F, ∀ i, 0 ≤ x i + b) : (shiftedNatSet F b).card = F.card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  funext i
  have hi := congrFun he i
  change (x i + b).toNat = (y i + b).toNat at hi
  have hx0 := hb x hx i
  have hy0 := hb y hy i
  omega

omit [Fintype ι] in
theorem integerShiftToNat_pdiff {F : Finset (ι → ℤ)} {b : ℤ}
    (hb : ∀ x ∈ F, ∀ i, 0 ≤ x i + b) {x y : ι → ℤ} (hx : x ∈ F) (hy : y ∈ F) :
    natVectorToInt (fun i ↦ integerShiftToNat b x i - integerShiftToNat b y i) = intPdiff x y := by
  funext i
  have hx0 := hb x hx i
  have hy0 := hb y hy i
  change (((x i + b).toNat - (y i + b).toNat : ℕ) : ℤ) = max (x i - y i) 0
  omega

theorem natVectorPositiveDifferences_shifted_image {F : Finset (ι → ℤ)} {b : ℤ}
    (hb : ∀ x ∈ F, ∀ i, 0 ≤ x i + b) :
    (natVectorPositiveDifferences (shiftedNatSet F b)).image natVectorToInt =
      integerPositiveDifferences F := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_natVectorPositiveDifferences.mp hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact mem_integerPositiveDifferences.mpr ⟨u, hu, v, hv, (integerShiftToNat_pdiff hb hu hv).symm⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerPositiveDifferences.mp hz
    apply Finset.mem_image.mpr
    refine ⟨(fun i ↦ integerShiftToNat b x i - integerShiftToNat b y i), ?_, integerShiftToNat_pdiff hb hx hy⟩
    exact mem_natVectorPositiveDifferences.mpr ⟨integerShiftToNat b x,
      Finset.mem_image_of_mem _ hx, integerShiftToNat b y, Finset.mem_image_of_mem _ hy, rfl⟩

theorem natVectorPositiveDifferences_shifted_card {F : Finset (ι → ℤ)} {b : ℤ}
    (hb : ∀ x ∈ F, ∀ i, 0 ≤ x i + b) :
    (natVectorPositiveDifferences (shiftedNatSet F b)).card = (integerPositiveDifferences F).card := by
  have he := congrArg Finset.card (natVectorPositiveDifferences_shifted_image hb)
  rw [Finset.card_image_of_injective _ natVectorToInt_injective] at he
  exact he

/-- Every integer-vector set is realized by positive integers supported on
any chosen distinct primes, preserving both relevant cardinalities. -/
theorem exists_prime_realization (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime) (F : Finset (ι → ℤ)) :
    ∃ A : Finset ℕ, A.card = F.card ∧ (cofactors A).card = (integerPositiveDifferences F).card ∧
      (∀ a ∈ A, 0 < a ∧ ∀ q ∈ a.factorization.support, q ∈ Set.range p) := by
  classical
  obtain ⟨b, hb⟩ := exists_nonnegative_shift F
  let T := shiftedNatSet F b
  refine ⟨T.image (primeEncode p), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (primeEncode_injective p hp)]
    exact shiftedNatSet_card hb
  · rw [cofactors_primeEncode_image_card p hp]
    exact natVectorPositiveDifferences_shifted_card hb
  · intro a ha
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨primeEncode_pos p hp x, ?_⟩
    intro q hq
    rw [primeEncode_factorization p hp] at hq
    exact primeExponentVector_support hq

end
end Erdos539Geometry
