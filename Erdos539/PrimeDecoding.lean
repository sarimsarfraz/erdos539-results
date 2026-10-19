/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerToNatural

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

/-- Positive integers whose prime divisors lie among the chosen primes. -/
def SupportedOnPrimes (p : ι ↪ ℕ) (a : ℕ) : Prop :=
  0 < a ∧ ∀ q ∈ a.factorization.support, q ∈ Set.range p

def exponentsOnPrimes (p : ι ↪ ℕ) (a : ℕ) : ι → ℕ := fun i ↦ a.factorization (p i)

theorem primeExponentVector_exponentsOnPrimes (p : ι ↪ ℕ) {a : ℕ}
    (ha : SupportedOnPrimes p a) :
    primeExponentVector p (exponentsOnPrimes p a) = a.factorization := by
  ext q
  by_cases hq : q ∈ Set.range p
  · obtain ⟨i, rfl⟩ := hq
    exact primeExponentVector_apply p _ i
  · have hzero : a.factorization q = 0 :=
      Finsupp.notMem_support_iff.mp (fun hs ↦ hq (ha.2 q hs))
    rw [hzero]
    exact Finsupp.embDomain_notin_range p _ q hq

theorem primeEncode_exponentsOnPrimes (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime) {a : ℕ}
    (ha : SupportedOnPrimes p a) : primeEncode p (exponentsOnPrimes p a) = a := by
  apply Nat.factorization_inj (primeEncode_pos p hp _).ne' ha.1.ne'
  rw [primeEncode_factorization p hp, primeExponentVector_exponentsOnPrimes p ha]

theorem exponentsOnPrimes_injOn (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime) {A : Finset ℕ}
    (hA : ∀ a ∈ A, SupportedOnPrimes p a) : (A : Set ℕ).InjOn (exponentsOnPrimes p) := by
  intro a ha b hb he
  rw [← primeEncode_exponentsOnPrimes p hp (hA a ha),
    ← primeEncode_exponentsOnPrimes p hp (hA b hb), he]

/-- Natural-vector positive differences commute with the injection into integers. -/
theorem integerPositiveDifferences_natVectorToInt_image (T : Finset (ι → ℕ)) :
    integerPositiveDifferences (T.image natVectorToInt) =
      (natVectorPositiveDifferences T).image natVectorToInt := by
  classical
  have hdiff (x y : ι → ℕ) :
      intPdiff (natVectorToInt x) (natVectorToInt y) = natVectorToInt (fun i ↦ x i - y i) := by
    funext i
    change max ((x i : ℤ) - y i) 0 = ((x i - y i : ℕ) : ℤ)
    omega
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerPositiveDifferences.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨(fun i ↦ u i - v i), ?_, (hdiff u v).symm⟩
    exact mem_natVectorPositiveDifferences.mpr ⟨u, hu, v, hv, rfl⟩
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_natVectorPositiveDifferences.mp hw
    exact mem_integerPositiveDifferences.mpr ⟨natVectorToInt u,
      Finset.mem_image_of_mem _ hu, natVectorToInt v,
      Finset.mem_image_of_mem _ hv, hdiff u v⟩

/-- The converse dictionary preserves the set size and the cofactor count. -/
theorem exists_integer_model_on_primes (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime)
    {A : Finset ℕ} (hA : ∀ a ∈ A, SupportedOnPrimes p a) :
    ∃ F : Finset (ι → ℤ), F.card = A.card ∧ (integerPositiveDifferences F).card = (cofactors A).card := by
  classical
  let T := A.image (exponentsOnPrimes p)
  have hT : T.card = A.card := Finset.card_image_of_injOn (exponentsOnPrimes_injOn p hp hA)
  have hencode : T.image (primeEncode p) = A := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      rwa [primeEncode_exponentsOnPrimes p hp (hA b hb)]
    · intro ha
      exact Finset.mem_image.mpr ⟨exponentsOnPrimes p a,
        Finset.mem_image_of_mem _ ha, primeEncode_exponentsOnPrimes p hp (hA a ha)⟩
  refine ⟨T.image natVectorToInt, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ natVectorToInt_injective, hT]
  · rw [integerPositiveDifferences_natVectorToInt_image,
      Finset.card_image_of_injective _ natVectorToInt_injective,
      ← cofactors_primeEncode_image_card p hp T, hencode]

end
end Erdos539Geometry
