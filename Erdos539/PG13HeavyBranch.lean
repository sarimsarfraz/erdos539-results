/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13RealBranches
import Erdos539.EnergyHereditary

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable [DecidableEq (Fin 13 → ℝ)]

theorem pg13_branch_mass_sum {T : ℕ} (hT : 0 < T)
    {f : integerRealSet (pg13Union T) → ℝ} (hf : f ∈ admissibleWeights (integerRealSet (pg13Union T))) :
    (∑ l : Fin 13, weightSquareSum (integerRealSet (pg13Branch T l))
      (extendWeight (integerRealSet (pg13Union T)) f)) = 1 := by
  have hdisj : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint
      (fun l ↦ integerRealSet (pg13Branch T l)) := by
    intro l _ m _ hlm
    exact pg13_real_branches_disjoint hT hlm
  calc
    _ = weightSquareSum (Finset.univ.biUnion (fun l : Fin 13 ↦ integerRealSet (pg13Branch T l)))
      (extendWeight (integerRealSet (pg13Union T)) f) := by
        unfold weightSquareSum
        exact (Finset.sum_biUnion hdisj).symm
    _ = weightSquareSum (integerRealSet (pg13Union T))
      (extendWeight (integerRealSet (pg13Union T)) f) := by
        congr 1
        ext x
        simp only [mem_integerRealSet, pg13Union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        aesop
    _ = 1 := by rw [weightSquareSum_extend]; exact hf.2

theorem pg13_exists_heavy_branch {T : ℕ} (hT : 0 < T)
    {f : integerRealSet (pg13Union T) → ℝ} (hf : f ∈ admissibleWeights (integerRealSet (pg13Union T))) :
    ∃ l : Fin 13, (1 / 13 : ℝ) ≤ weightSquareSum (integerRealSet (pg13Branch T l))
      (extendWeight (integerRealSet (pg13Union T)) f) := by
  by_contra h
  push_neg at h
  have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (by simp : (Finset.univ : Finset (Fin 13)).Nonempty) (fun l _ ↦ h l)
  rw [pg13_branch_mass_sum hT hf] at hs
  norm_num at hs

/-- At least one actual branch retains at least 1/169 of the union norm.
This uses an exact optimizer and its actual branch mass. -/
theorem pg13_exists_branch_norm_retention {T : ℕ} (hT : 0 < T) :
    ∃ l : Fin 13, energyNorm (integerRealSet (pg13Union T)) ≤
      169 * energyNorm (integerRealSet (pg13Branch T l)) := by
  have hU := integerRealSet_nonempty (pg13Union_nonempty hT)
  obtain ⟨f, hf, hs, hE⟩ := energyNorm_attained hU
  obtain ⟨l, hl⟩ := pg13_exists_heavy_branch hT ⟨hf, hs⟩
  have hret := energyNorm_hereditary (pg13Branch_real_subset T l) hU ⟨hf, hs⟩ hE
  have hm : (1 / 169 : ℝ) ≤ weightSquareSum (integerRealSet (pg13Branch T l))
      (extendWeight (integerRealSet (pg13Union T)) f) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hm (energyNorm_nonneg (integerRealSet (pg13Union T)))
  exact ⟨l, by nlinarith⟩

end
end Erdos539Geometry
