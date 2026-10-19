/-
Copyright 2026 Kenta Kitamura
SPDX-License-Identifier: Apache-2.0
Adapted imports for Lean v4.29.0-rc8 by Sarim Sarfraz and Codex.
See vendor-sources/kitamura-sqrt/SOURCE.json.
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

/-!
# Prime exponent model for Erdős problem 539

This file contains only unconditional bridge lemmas.  It does not assume any
lower bound for a positive-difference set.
-/

namespace Erdos539Geometry


noncomputable section

attribute [local instance] Classical.propDecidable

/-- The cofactors appearing in Erdős problem 539. -/
def cofactors (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image fun (a, b) ↦ a / a.gcd b

/-- Prime exponent vectors of the members of a finite set. -/
def exponentSet (A : Finset ℕ) : Finset (ℕ →₀ ℕ) :=
  A.image Nat.factorization

/-- Coordinatewise positive differences, represented by natural subtraction. -/
def positiveDifferences (F : Finset (ℕ →₀ ℕ)) : Finset (ℕ →₀ ℕ) :=
  (F ×ˢ F).image fun (x, y) ↦ x - y

theorem cofactor_pos {a b : ℕ} (ha : 0 < a) : 0 < a / a.gcd b :=
  Nat.div_pos (Nat.gcd_le_left b ha) (Nat.gcd_pos_of_pos_left b ha)

/-- Division by the gcd becomes coordinatewise truncated subtraction. -/
theorem factorization_cofactor {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a / a.gcd b).factorization = a.factorization - b.factorization := by
  rw [Nat.factorization_div (Nat.gcd_dvd_left a b),
    Nat.factorization_gcd ha.ne' hb.ne']
  ext p
  simp only [Finsupp.tsub_apply, Finsupp.inf_apply]
  omega

theorem exponentSet_card {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    (exponentSet A).card = A.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact Nat.factorization_inj (hA a ha).ne' (hA b hb).ne' hab

theorem cofactors_pos {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    ∀ c ∈ cofactors A, 0 < c := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨⟨a,b⟩, hab, rfl⟩
  exact cofactor_pos (hA a (Finset.mem_product.mp hab).1)

/-- The factorization image is exactly the positive-difference set. -/
theorem exponentSet_cofactors {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    exponentSet (cofactors A) = positiveDifferences (exponentSet A) := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨c, hc, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨⟨a,b⟩, hab, rfl⟩
    have ha := (Finset.mem_product.mp hab).1
    have hb := (Finset.mem_product.mp hab).2
    apply Finset.mem_image.mpr
    refine ⟨(a.factorization, b.factorization), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ha,
        Finset.mem_image_of_mem _ hb⟩
    · exact (factorization_cofactor (hA a ha) (hA b hb)).symm
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨⟨x,y⟩, hxy, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hxy).1 with ⟨a,ha,rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hxy).2 with ⟨b,hb,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨a / a.gcd b, ?_, factorization_cofactor (hA a ha) (hA b hb)⟩
    exact Finset.mem_image_of_mem (fun (ab : ℕ × ℕ) ↦ ab.1 / ab.1.gcd ab.2)
      (Finset.mem_product.mpr ⟨ha,hb⟩ : (a,b) ∈ A ×ˢ A)

/-- No cofactor cardinality is lost in the prime exponent model. -/
theorem positiveDifferences_exponentSet_card {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a) :
    (positiveDifferences (exponentSet A)).card = (cofactors A).card := by
  rw [← exponentSet_cofactors hA]
  exact exponentSet_card (cofactors_pos hA)

/-- All coordinates used by members of a finite set of exponent vectors. -/
def coordinateSupport (F : Finset (ℕ →₀ ℕ)) : Finset ℕ :=
  F.biUnion Finsupp.support

/-- Restriction to a finite set of coordinates, with real-valued entries. -/
def realRestriction (S : Finset ℕ) (x : ℕ →₀ ℕ) : S → ℝ :=
  fun p ↦ x p

/-- Positive differences of finite-dimensional real vectors. -/
def realPositiveDifferences {ι : Type*} (F : Finset (ι → ℝ)) :
    Finset (ι → ℝ) := by
  classical
  exact (F ×ˢ F).image fun (x,y) i ↦ max (x i - y i) 0

theorem support_subset_coordinateSupport {F : Finset (ℕ →₀ ℕ)} {x : ℕ →₀ ℕ}
    (hx : x ∈ F) : x.support ⊆ coordinateSupport F := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨x,hx,hp⟩

theorem positiveDifferences_support_subset {F : Finset (ℕ →₀ ℕ)} {x : ℕ →₀ ℕ}
    (hx : x ∈ positiveDifferences F) : x.support ⊆ coordinateSupport F := by
  rcases Finset.mem_image.mp hx with ⟨⟨a,b⟩,hab,rfl⟩
  exact Finsupp.support_tsub.trans
    (support_subset_coordinateSupport (Finset.mem_product.mp hab).1)

theorem realRestriction_injective {S : Finset ℕ} {x y : ℕ →₀ ℕ}
    (hx : x.support ⊆ S) (hy : y.support ⊆ S)
    (hxy : realRestriction S x = realRestriction S y) : x = y := by
  ext p
  by_cases hp : p ∈ S
  · have h := congrFun hxy ⟨p,hp⟩
    change (x p : ℝ) = (y p : ℝ) at h
    exact_mod_cast h
  · have hx0 : x p = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hp (hx h))
    have hy0 : y p = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hp (hy h))
    rw [hx0,hy0]

theorem realRestriction_card {S : Finset ℕ} {F : Finset (ℕ →₀ ℕ)}
    (hF : ∀ x ∈ F, x.support ⊆ S) :
    (F.image (realRestriction S)).card = F.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  exact realRestriction_injective (hF x hx) (hF y hy) hxy

theorem nat_sub_cast (a b : ℕ) : ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hab : a ≤ b := le_of_not_ge h
    rw [Nat.sub_eq_zero_of_le hab, Nat.cast_zero, max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast hab)

theorem realRestriction_sub (S : Finset ℕ) (x y : ℕ →₀ ℕ) :
    realRestriction S (x-y) = fun i ↦ max (realRestriction S x i -
      realRestriction S y i) 0 := by
  funext i
  exact nat_sub_cast (x i) (y i)

theorem realPositiveDifferences_image (S : Finset ℕ) (F : Finset (ℕ →₀ ℕ)) :
    realPositiveDifferences (F.image (realRestriction S)) =
      (positiveDifferences F).image (realRestriction S) := by
  classical
  ext v
  simp only [realPositiveDifferences, positiveDifferences, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x,y⟩, ⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩, rfl⟩
    exact ⟨a-b,⟨(a,b),⟨ha,hb⟩,rfl⟩,realRestriction_sub S a b⟩
  · rintro ⟨c,⟨⟨a,b⟩,hab,rfl⟩,rfl⟩
    refine ⟨(realRestriction S a, realRestriction S b), ?_, ?_⟩
    · exact ⟨⟨a,hab.1,rfl⟩,⟨b,hab.2,rfl⟩⟩
    · exact (realRestriction_sub S a b).symm

/-- A finite real-vector realization of an integer cofactor problem. -/
def realExponentSet (A : Finset ℕ) :
    Finset (coordinateSupport (exponentSet A) → ℝ) :=
  (exponentSet A).image (realRestriction (coordinateSupport (exponentSet A)))

theorem realExponentSet_card {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    (realExponentSet A).card = A.card := by
  rw [realExponentSet, realRestriction_card
    (fun _ hx ↦ support_subset_coordinateSupport hx)]
  exact exponentSet_card hA

theorem realPositiveDifferences_realExponentSet_card {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a) :
    (realPositiveDifferences (realExponentSet A)).card = (cofactors A).card := by
  rw [realExponentSet, realPositiveDifferences_image,
    realRestriction_card (fun _ hx ↦ positiveDifferences_support_subset hx)]
  exact positiveDifferences_exponentSet_card hA

/-- Restriction to a finite set of coordinates, with integer-valued entries. -/
def integerRestriction (S : Finset ℕ) (x : ℕ →₀ ℕ) : S → ℤ :=
  fun p ↦ x p

/-- Positive differences of finite-dimensional integer vectors. -/
def integerPositiveDifferences {ι : Type*} (F : Finset (ι → ℤ)) :
    Finset (ι → ℤ) := by
  classical
  exact (F ×ˢ F).image fun (x,y) i ↦ max (x i - y i) 0

theorem integerRestriction_injective {S : Finset ℕ} {x y : ℕ →₀ ℕ}
    (hx : x.support ⊆ S) (hy : y.support ⊆ S)
    (hxy : integerRestriction S x = integerRestriction S y) : x = y := by
  ext p
  by_cases hp : p ∈ S
  · have h := congrFun hxy ⟨p,hp⟩
    change (x p : ℤ) = (y p : ℤ) at h
    exact_mod_cast h
  · have hx0 : x p = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hp (hx h))
    have hy0 : y p = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hp (hy h))
    rw [hx0,hy0]

theorem integerRestriction_card {S : Finset ℕ} {F : Finset (ℕ →₀ ℕ)}
    (hF : ∀ x ∈ F, x.support ⊆ S) :
    (F.image (integerRestriction S)).card = F.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  exact integerRestriction_injective (hF x hx) (hF y hy) hxy

theorem nat_sub_cast_int (a b : ℕ) : ((a - b : ℕ) : ℤ) = max ((a : ℤ) - b) 0 := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hab : a ≤ b := le_of_not_ge h
    rw [Nat.sub_eq_zero_of_le hab, Nat.cast_zero, max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast hab)

theorem integerRestriction_sub (S : Finset ℕ) (x y : ℕ →₀ ℕ) :
    integerRestriction S (x-y) = fun i ↦ max (integerRestriction S x i -
      integerRestriction S y i) 0 := by
  funext i
  exact nat_sub_cast_int (x i) (y i)

theorem integerPositiveDifferences_image (S : Finset ℕ) (F : Finset (ℕ →₀ ℕ)) :
    integerPositiveDifferences (F.image (integerRestriction S)) =
      (positiveDifferences F).image (integerRestriction S) := by
  classical
  ext v
  simp only [integerPositiveDifferences, positiveDifferences, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x,y⟩, ⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩, rfl⟩
    exact ⟨a-b,⟨(a,b),⟨ha,hb⟩,rfl⟩,integerRestriction_sub S a b⟩
  · rintro ⟨c,⟨⟨a,b⟩,hab,rfl⟩,rfl⟩
    refine ⟨(integerRestriction S a, integerRestriction S b), ?_, ?_⟩
    · exact ⟨⟨a,hab.1,rfl⟩,⟨b,hab.2,rfl⟩⟩
    · exact (integerRestriction_sub S a b).symm

/-- A finite integer-vector realization of an integer cofactor problem. -/
def integerExponentSet (A : Finset ℕ) :
    Finset (coordinateSupport (exponentSet A) → ℤ) :=
  (exponentSet A).image (integerRestriction (coordinateSupport (exponentSet A)))

theorem integerExponentSet_card {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    (integerExponentSet A).card = A.card := by
  rw [integerExponentSet, integerRestriction_card
    (fun _ hx ↦ support_subset_coordinateSupport hx)]
  exact exponentSet_card hA

theorem integerPositiveDifferences_integerExponentSet_card {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a) :
    (integerPositiveDifferences (integerExponentSet A)).card = (cofactors A).card := by
  rw [integerExponentSet, integerPositiveDifferences_image,
    integerRestriction_card (fun _ hx ↦ positiveDifferences_support_subset hx)]
  exact positiveDifferences_exponentSet_card hA

/-- Ordinary differences of integer vectors. -/
def integerDifferences {ι : Type*} (F : Finset (ι → ℤ)) : Finset (ι → ℤ) := by
  classical
  exact (F ×ˢ F).image fun (x,y) i ↦ x i - y i

/-- A difference is determined by its positive and negative parts. -/
theorem integerDifferences_card_le {ι : Type*} (F : Finset (ι → ℤ)) :
    (integerDifferences F).card ≤ (integerPositiveDifferences F).card ^ 2 := by
  classical
  let split : (ι → ℤ) → (ι → ℤ) × (ι → ℤ) :=
    fun z ↦ (fun i ↦ max (z i) 0, fun i ↦ max (-z i) 0)
  have h : (integerDifferences F).card ≤
      (integerPositiveDifferences F ×ˢ integerPositiveDifferences F).card := by
    apply Finset.card_le_card_of_injOn split
    · intro z hz
      rcases Finset.mem_image.mp hz with ⟨⟨x,y⟩,hxy,rfl⟩
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨(x,y),hxy,rfl⟩
      · refine Finset.mem_image.mpr ⟨(y,x),?_,?_⟩
        · exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hxy).2,
            (Finset.mem_product.mp hxy).1⟩
        · funext i
          dsimp [split]
          congr 1
          omega
    · intro z hz w hw hzw
      have hp := congrArg Prod.fst hzw
      have hn := congrArg Prod.snd hzw
      funext i
      have hpi := congrFun hp i
      have hni := congrFun hn i
      dsimp [split] at hpi hni
      omega
  simpa only [Finset.card_product, pow_two] using h

theorem integerDifferences_integerExponentSet_card_le {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a) :
    (integerDifferences (integerExponentSet A)).card ≤ (cofactors A).card ^ 2 := by
  simpa only [integerPositiveDifferences_integerExponentSet_card hA] using
    integerDifferences_card_le (integerExponentSet A)

/-- The coordinatewise inclusion of integer vectors in real vectors. -/
def integerToReal {ι : Type*} (x : ι → ℤ) : ι → ℝ := fun i ↦ x i

theorem integerToReal_injective {ι : Type*} :
    Function.Injective (integerToReal (ι := ι)) := by
  intro x y hxy
  funext i
  have h := congrFun hxy i
  change (x i : ℝ) = (y i : ℝ) at h
  exact_mod_cast h

theorem integerToReal_image_card {ι : Type*} (F : Finset (ι → ℤ)) :
    (F.image integerToReal).card = F.card := by
  classical
  exact Finset.card_image_of_injective _ integerToReal_injective

theorem realPositiveDifferences_integerToReal_image {ι : Type*} (F : Finset (ι → ℤ)) :
    realPositiveDifferences (F.image integerToReal) =
      (integerPositiveDifferences F).image integerToReal := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨⟨x,y⟩,hxy,rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hxy).1 with ⟨a,ha,rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hxy).2 with ⟨b,hb,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(fun i ↦ max (a i - b i) 0), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩
    · funext i
      simp [integerToReal]
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨c,hc,rfl⟩
    rcases Finset.mem_image.mp hc with ⟨⟨a,b⟩,hab,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(integerToReal a, integerToReal b), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ (Finset.mem_product.mp hab).1,
         Finset.mem_image_of_mem _ (Finset.mem_product.mp hab).2⟩
    · funext i
      simp [integerToReal]

theorem realPositiveDifferences_integerToReal_image_card {ι : Type*}
    (F : Finset (ι → ℤ)) :
    (realPositiveDifferences (F.image integerToReal)).card =
      (integerPositiveDifferences F).card := by
  classical
  rw [realPositiveDifferences_integerToReal_image, integerToReal_image_card]

end
end Erdos539Geometry

#print axioms Erdos539Geometry.factorization_cofactor
#print axioms Erdos539Geometry.exponentSet_card
#print axioms Erdos539Geometry.positiveDifferences_exponentSet_card

#print axioms Erdos539Geometry.realExponentSet_card
#print axioms Erdos539Geometry.realPositiveDifferences_realExponentSet_card

#print axioms Erdos539Geometry.integerExponentSet_card
#print axioms Erdos539Geometry.integerPositiveDifferences_integerExponentSet_card

#print axioms Erdos539Geometry.integerDifferences_integerExponentSet_card_le
#print axioms Erdos539Geometry.realPositiveDifferences_integerToReal_image_card
