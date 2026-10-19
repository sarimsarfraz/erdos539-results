/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductEnergy
import Erdos539.EnergySupport

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def rowPointAtomWeight (r : ℝ) (x : G) : ℝ := if x = 0 then r else 0

theorem mixedWeightedEnergy_point_cross (S : Finset G) (h0 : (0 : G) ∈ S)
    (f : G → ℝ) (r : ℝ) :
    mixedWeightedEnergy S f (rowPointAtomWeight r) f (rowPointAtomWeight r) = r ^ 2 * weightSquareSum S f := by
  rw [mixedWeightedEnergy_eq_quadruples]
  have ht (a b c d : G) :
      (if a + b = c + d then (f a * rowPointAtomWeight r b) * (f c * rowPointAtomWeight r d) else 0) =
        if b = 0 then if d = 0 then if c = a then r ^ 2 * f a ^ 2 else 0 else 0 else 0 := by
    by_cases hb : b = 0
    · subst b
      by_cases hd : d = 0
      · subst d
        by_cases hc : c = a
        · subst c; simp [rowPointAtomWeight]; ring
        · simp [hc, Ne.symm hc]
      · simp [rowPointAtomWeight, hd]
    · simp [rowPointAtomWeight, hb]
  simp only [Finset.sum_product, ht]
  simp [h0, weightSquareSum, ← Finset.mul_sum]

theorem weightedEnergy_point (S : Finset G) (h0 : (0 : G) ∈ S) (r : ℝ) :
    weightedEnergy S (rowPointAtomWeight r) = r ^ 4 := by
  rw [← mixedWeightedEnergy_self, mixedWeightedEnergy_point_cross S h0]
  simp [weightSquareSum, rowPointAtomWeight, h0, pow_succ]
  ring

def rowPointWeight (f : G → ℝ) (r : ℝ) (p : G × ℤ) : ℝ :=
  if p.2 = 0 then f p.1 else rowPointAtomWeight r p.1

/-- A row at height zero and one point at height one. -/
def rowPointSupport (S : Finset G) : Finset (G × ℤ) :=
  (S ×ˢ ({0} : Finset ℤ)) ∪ {(0, 1)}

theorem rowPointSupport_subset (S : Finset G) (h0 : (0 : G) ∈ S) :
    rowPointSupport S ⊆ S ×ˢ ({0, 1} : Finset ℤ) := by
  intro p hp
  simp only [rowPointSupport, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_insert] at hp ⊢
  rcases hp with ⟨hs, hz⟩ | rfl
  · exact ⟨hs, Or.inl hz⟩
  · exact ⟨h0, Or.inr rfl⟩

theorem rowPointWeight_zero (S : Finset G) (f : G → ℝ) (r : ℝ)
    (p : G × ℤ) (hp : p ∈ S ×ˢ ({0, 1} : Finset ℤ)) (hn : p ∉ rowPointSupport S) :
    rowPointWeight f r p = 0 := by
  simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hp
  have hz : p.2 ≠ 0 := by
    intro he
    exact hn (Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hp.1, by simpa using he⟩))
  have hx : p.1 ≠ 0 := by
    intro he
    have hy : p.2 = 1 := hp.2.resolve_left hz
    exact hn (Finset.mem_union_right _ (Finset.mem_singleton.mpr (Prod.ext he hy)))
  simp [rowPointWeight, hz, rowPointAtomWeight, hx]

end
end Erdos539Geometry
