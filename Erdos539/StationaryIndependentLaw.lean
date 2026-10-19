/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryLawCorrelation
import Erdos539.FiniteEntropyMixtures

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G]

/-- The literal additive law (X,Y,X,Y) for independent endpoints of law
nu. This also supplies a feasible law when some endpoint atoms vanish. -/
def independentStationaryAdditiveLaw (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : StationaryAdditiveLaw S ν where
  mass a b c d := if a = c then if b = d then ν a * ν b else 0 else 0
  nonneg := by
    intro a b c d
    split_ifs
    · exact mul_nonneg (hν a) (hν b)
    · rfl
    · rfl
  supported := by
    intro a b c d h
    split_ifs with hac hbd
    · subst c; subst d; exact (h rfl).elim
    · rfl
    · rfl
  first := by
    intro a
    have hs' : ∑ x ∈ S.attach, ν x = 1 := hs
    simp [← Finset.mul_sum, hs']
  second := by
    intro b
    have hs' : ∑ x ∈ S.attach, ν x = 1 := hs
    simp [← Finset.sum_mul, hs']
  third := by
    intro c
    have hs' : ∑ x ∈ S.attach, ν x = 1 := hs
    simp [← Finset.mul_sum, hs']
  fourth := by
    intro d
    have hs' : ∑ x ∈ S.attach, ν x = 1 := hs
    simp [← Finset.sum_mul, hs']

theorem independentStationaryAdditiveLaw_entropy (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    (independentStationaryAdditiveLaw S ν hν hs).entropy = 2 * finiteEntropy ν := by
  have h := finiteEntropy_rows ν (fun _ ↦ ν) (fun _ ↦ hs)
  simp only [← Finset.sum_mul, hs, one_mul] at h
  have he : (independentStationaryAdditiveLaw S ν hν hs).entropy =
      finiteEntropy (fun z : S × S ↦ ν z.1 * ν z.2) := by
    simp [StationaryAdditiveLaw.entropy, independentStationaryAdditiveLaw,
      finiteEntropy, Fintype.sum_prod_type, apply_ite Real.negMulLog]
  rw [he, h]
  ring

end
end Erdos539Geometry
