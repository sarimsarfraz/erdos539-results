/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteSupportCost
import Erdos539.StationaryLawCorrelation
import Erdos539.ReflectedSupportCertificate

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def reflectedLawMass (S : Finset G) (ν : S → ℝ) (w : G) : ℝ :=
  ∑ x : S, if w - x.val ∈ S then ν x else 0

theorem reflectedLawMass_nonneg (S : Finset G) (ν : S → ℝ) (hν : ∀ x, 0 ≤ ν x) (w : G) :
    0 ≤ reflectedLawMass S ν w := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact hν x
  · exact le_rfl

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

theorem triple_reflected_support (Q : StationaryAdditiveLaw S ν)
    {z : (S × S) × S} (hz : Q.triple.mass z ≠ 0) : z.1.1.val + z.1.2.val - z.2.val ∈ S := by
  by_contra hn
  apply hz
  apply finitePush_eq_zero_of_fiber_zero
  intro y hy
  subst z
  apply Q.supported
  intro hrel
  have he : y.1.1.val + y.1.2.val - y.2.1.val = y.2.2.val := by rw [hrel]; abel
  exact hn (he.symm ▸ y.2.2.property)

/-- A direct support-cost proof of reflected retention: the triple law is
supported where its third endpoint belongs to the reflection at the first
pair's sum. This applies to every actual stationary additive law. -/
theorem correlation_ge_reflected_mass_cost (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) {r : ℝ}
    (hr : ∀ w : G, reflectedLawMass S ν w ≤ r) : -Real.log r ≤ Q.correlation := by
  let E : (S × S) × S → Prop := fun z ↦ z.1.1.val + z.1.2.val - z.2.val ∈ S
  letI : DecidablePred E := fun z ↦ Classical.propDecidable (E z)
  have hmass : (∑ z, Q.triple.mass z) = 1 := by
    rw [← finitePush_sum Q.triple.mass (fun z ↦ z.1.1), Q.triple.first, hs]
  have hm : (∑ z, if E z then independentTriple ν z else 0) ≤ r := by
    calc
      _ = ∑ a : S, ∑ b : S, (ν a * ν b) * reflectedLawMass S ν (a.val + b.val) := by
        simp only [Fintype.sum_prod_type, E, independentTriple, reflectedLawMass,
          Finset.mul_sum, mul_ite, mul_zero]
      _ ≤ ∑ a : S, ∑ b : S, (ν a * ν b) * r := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hr _) (mul_nonneg (hν a) (hν b))
      _ = r := by simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul]
  have h := finiteRelEntropy_ge_support_cost Q.triple.mass (independentTriple ν) Q.triple.nonneg
    (fun z ↦ mul_nonneg (mul_nonneg (hν z.1.1) (hν z.1.2)) (hν z.2)) hmass E
    (fun _ hz ↦ Q.triple_reflected_support hz) (fun _ hz ↦ Q.triple.reference_pos hz) hm
  rw [Q.triple.relativeEntropy_eq, Q.triple_entropy_eq] at h
  exact h

end StationaryAdditiveLaw
end
end Erdos539Geometry
