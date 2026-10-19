/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerGeometry
import Mathlib.Data.Finsupp.Order

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Finite ι]

/-- Natural exponent vectors supported on the chosen distinct primes. -/
def primeExponentVector (p : ι ↪ ℕ) (x : ι → ℕ) : ℕ →₀ ℕ :=
  Finsupp.embDomain p (Finsupp.equivFunOnFinite.symm x)

def primeEncode (p : ι ↪ ℕ) (x : ι → ℕ) : ℕ :=
  (primeExponentVector p x).prod (fun q e ↦ q ^ e)

@[simp] theorem primeExponentVector_apply (p : ι ↪ ℕ) (x : ι → ℕ) (i : ι) :
    primeExponentVector p x (p i) = x i := by
  simp only [primeExponentVector, Finsupp.embDomain_apply_self, Finsupp.coe_equivFunOnFinite_symm]

theorem primeExponentVector_support {p : ι ↪ ℕ} {x : ι → ℕ} {q : ℕ}
    (hq : q ∈ (primeExponentVector p x).support) : q ∈ Set.range p := by
  obtain ⟨i, _hi, hqi⟩ := Finset.mem_map.mp hq
  exact ⟨i, hqi⟩

theorem primeEncode_factorization (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime) (x : ι → ℕ) :
    (primeEncode p x).factorization = primeExponentVector p x := by
  apply Nat.prod_pow_factorization_eq_self
  intro q hq
  obtain ⟨i, rfl⟩ := primeExponentVector_support hq
  exact hp i

theorem primeEncode_pos (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime) (x : ι → ℕ) :
    0 < primeEncode p x := by
  apply Nat.prod_pow_pos_of_zero_notMem_support
  intro hq
  obtain ⟨i, hi⟩ := primeExponentVector_support hq
  exact (hp i).ne_zero hi

theorem primeEncode_injective (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    Function.Injective (primeEncode p) := by
  intro x y he
  have hv := congrArg Nat.factorization he
  rw [primeEncode_factorization p hp, primeEncode_factorization p hp] at hv
  funext i
  have hi := DFunLike.congr_fun hv (p i)
  simpa only [primeExponentVector_apply] using hi

theorem primeExponentVector_sub (p : ι ↪ ℕ) (x y : ι → ℕ) :
    primeExponentVector p (fun i ↦ x i - y i) = primeExponentVector p x - primeExponentVector p y := by
  rw [primeExponentVector, primeExponentVector, primeExponentVector, ← Finsupp.embDomain_tsub]
  congr 1
  ext i
  rfl

/-- The arithmetic quotient is exactly coordinatewise truncated subtraction. -/
theorem primeEncode_cofactor (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime) (x y : ι → ℕ) :
    primeEncode p x / (primeEncode p x).gcd (primeEncode p y) =
      primeEncode p (fun i ↦ x i - y i) := by
  apply Nat.factorization_inj (cofactor_pos (primeEncode_pos p hp x)).ne'
    (primeEncode_pos p hp _).ne'
  rw [factorization_cofactor (primeEncode_pos p hp x) (primeEncode_pos p hp y),
    primeEncode_factorization p hp, primeEncode_factorization p hp,
    primeEncode_factorization p hp, primeExponentVector_sub]

def natVectorPositiveDifferences (F : Finset (ι → ℕ)) : Finset (ι → ℕ) :=
  (F ×ˢ F).image (fun p i ↦ p.1 i - p.2 i)

omit [Finite ι] in
@[simp] theorem mem_natVectorPositiveDifferences {F : Finset (ι → ℕ)} {u : ι → ℕ} :
    u ∈ natVectorPositiveDifferences F ↔ ∃ x ∈ F, ∃ y ∈ F, (fun i ↦ x i - y i) = u := by
  classical
  simp only [natVectorPositiveDifferences, Finset.mem_image, Prod.exists, Finset.mem_product]
  aesop

theorem cofactors_primeEncode_image (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime)
    (F : Finset (ι → ℕ)) :
    cofactors (F.image (primeEncode p)) = (natVectorPositiveDifferences F).image (primeEncode p) := by
  classical
  ext q
  simp only [cofactors, natVectorPositiveDifferences, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
    exact ⟨(fun i ↦ x i - y i), ⟨x, y, ⟨hx, hy⟩, rfl⟩, (primeEncode_cofactor p hp x y).symm⟩
  · rintro ⟨z, ⟨x, y, ⟨hx, hy⟩, rfl⟩, rfl⟩
    exact ⟨primeEncode p x, primeEncode p y,
      ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, primeEncode_cofactor p hp x y⟩

theorem cofactors_primeEncode_image_card (p : ι ↪ ℕ) (hp : ∀ i, (p i).Prime)
    (F : Finset (ι → ℕ)) :
    (cofactors (F.image (primeEncode p))).card = (natVectorPositiveDifferences F).card := by
  rw [cofactors_primeEncode_image p hp, Finset.card_image_of_injective _ (primeEncode_injective p hp)]

end
end Erdos539Geometry
