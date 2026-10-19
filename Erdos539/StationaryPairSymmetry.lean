/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyMaximum
import Erdos539.FiniteEntropyConcavity
import Erdos539.StationaryLawComposition

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G : Type*} [AddCommGroup G]

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

/-- Reverse both endpoint pairs simultaneously. -/
def pairReversal (Q : StationaryAdditiveLaw S ν) : StationaryAdditiveLaw S ν where
  mass a b c d := Q.mass b a d c
  nonneg a b c d := Q.nonneg b a d c
  supported a b c d h := Q.supported b a d c (by simpa only [add_comm] using h)
  first := by
    intro a
    calc
      (∑ b, ∑ c, ∑ d, Q.mass b a d c) = ∑ b, ∑ d, ∑ c, Q.mass b a d c := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_comm]
      _ = ν a := Q.second a
  second := by
    intro b
    calc
      (∑ a, ∑ c, ∑ d, Q.mass b a d c) = ∑ a, ∑ d, ∑ c, Q.mass b a d c := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = ν b := Q.first b
  third := by
    intro c
    rw [Finset.sum_comm]
    exact Q.fourth c
  fourth := by
    intro d
    rw [Finset.sum_comm]
    exact Q.third d

theorem pairReversal_entropy (Q : StationaryAdditiveLaw S ν) : Q.pairReversal.entropy = Q.entropy := by
  rw [Q.pairReversal.entropy_eq_finiteEntropy_flat, Q.entropy_eq_finiteEntropy_flat]
  unfold finiteEntropy
  apply Fintype.sum_equiv (Equiv.prodCongr (Equiv.prodComm S S) (Equiv.prodComm S S))
  intro x
  rfl

def pairSymmetrize (Q : StationaryAdditiveLaw S ν) : StationaryAdditiveLaw S ν where
  mass a b c d := (Q.mass a b c d + Q.pairReversal.mass a b c d) / 2
  nonneg a b c d := div_nonneg (add_nonneg (Q.nonneg a b c d) (Q.pairReversal.nonneg a b c d)) (by norm_num)
  supported a b c d h := by rw [Q.supported a b c d h, Q.pairReversal.supported a b c d h]; norm_num
  first := by
    intro a
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, Q.first, Q.pairReversal.first]
    ring
  second := by
    intro b
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, Q.second, Q.pairReversal.second]
    ring
  third := by
    intro c
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, Q.third, Q.pairReversal.third]
    ring
  fourth := by
    intro d
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, Q.fourth, Q.pairReversal.fourth]
    ring

theorem pairSymmetrize_symmetric (Q : StationaryAdditiveLaw S ν) (a b c d : S) :
    Q.pairSymmetrize.mass a b c d = Q.pairSymmetrize.mass b a d c := by
  simp only [pairSymmetrize, pairReversal]
  ring

theorem pairSymmetrize_entropy_ge (Q : StationaryAdditiveLaw S ν) : Q.entropy ≤ Q.pairSymmetrize.entropy := by
  have h := finiteEntropy_concave Q.flat Q.pairReversal.flat
    (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
    (fun t ↦ Q.pairReversal.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have he : (1 / 2 : ℝ) • Q.flat + (1 / 2 : ℝ) • Q.pairReversal.flat = Q.pairSymmetrize.flat := by
    funext t
    change (1 / 2 : ℝ) * Q.mass t.1.1 t.1.2 t.2.1 t.2.2 +
      (1 / 2 : ℝ) * Q.pairReversal.mass t.1.1 t.1.2 t.2.1 t.2.2 = _
    simp only [flat, pairSymmetrize]
    ring
  rw [he, ← Q.entropy_eq_finiteEntropy_flat, ← Q.pairReversal.entropy_eq_finiteEntropy_flat,
    ← Q.pairSymmetrize.entropy_eq_finiteEntropy_flat, Q.pairReversal_entropy] at h
  linarith

end StationaryAdditiveLaw

/-- The attained entropy maximum can be chosen invariant under simultaneous
pair reversal, including endpoint laws with zero atoms. -/
theorem exists_pair_symmetric_stationary_maximum (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    ∃ Q : StationaryAdditiveLaw S ν, Q.entropy = stationaryAdditiveEntropy S ν ∧
      ∀ a b c d, Q.mass a b c d = Q.mass b a d c := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  refine ⟨Q.pairSymmetrize, ?_, Q.pairSymmetrize_symmetric⟩
  apply le_antisymm (Q.pairSymmetrize.entropy_le_stationaryAdditiveEntropy hν hs)
  rw [← hQ]
  exact Q.pairSymmetrize_entropy_ge

end
end Erdos539Geometry
