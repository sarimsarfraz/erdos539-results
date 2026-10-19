/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProjectionBalance
import Erdos539.CoordinatePartition
import Erdos539.AggregatePruning
import Erdos539.LogPruning

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

/-- Aggregate regularity theorem with the uniform exponent `m / (2m - 1)`.
All descendants keep the original parent `S` and the same bound `H`. -/
theorem aggregate_log_bound {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (H : ℕ) (hH : ∀ J, (projection S J).card * maxFiber S (project J) ≤ H) :
    ∀ (m : ℕ) (I : Finset ι), (Finset.univ \ I).card = m → 0 < m →
      ∀ A ⊆ S, A.Nonempty →
        fanLogBound m A.card H (projection S I).card ≤ Real.log (maxRestrictedFan A I) := by
  classical
  have hSH : S.card ≤ H := parent_card_le_of_fiber_bound hS hH
  have hPpos (J : Finset ι) : (0 : ℝ) < (projection S J).card := by
    exact_mod_cast Finset.card_pos.mpr (hS.image (project J))
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro I hm hmpos A hAS hA
    have hn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hnH : (A.card : ℝ) ≤ H := by exact_mod_cast (Finset.card_le_card hAS).trans hSH
    have hMone : (1 : ℝ) ≤ maxRestrictedFan A I := by exact_mod_cast one_le_maxRestrictedFan hA I
    have hM : (0 : ℝ) < maxRestrictedFan A I := by linarith
    by_cases hsmall : A.card ≤ (projection S I).card
    · exact fanLogBound_le_of_small_fiber hmpos hn hnH (by exact_mod_cast hsmall) hMone
    have hPn : ((projection S I).card : ℝ) ≤ A.card := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hsmall))
    by_cases hmone : m = 1
    · obtain ⟨i, hi⟩ := exists_one_free_coordinate (hm.trans hmone)
      rw [hmone]
      apply fanLogBound_one hn (hPpos I) hM
      exact_mod_cast card_le_projection_mul_restrictedFan_one_free hAS I i hi
    have hm2 : 2 ≤ m := by omega
    obtain ⟨U, hU, hbU, hbV⟩ := relative_projection_balance hAS hA I H hH
    let V := (Finset.univ \ I) \ U
    have hremU : Finset.univ \ (I ∪ U) = V := remaining_union I U
    have hremV : Finset.univ \ (I ∪ V) = U := remaining_union_complement I hU
    have hdim : U.card + V.card = m := (partition_card I hU).trans hm
    have hbU' : (A.card : ℝ) * (projection S (I ∪ U)).card ≤
        ((4 * 2 ^ m : ℕ) : ℝ) * H * maxRestrictedFan A I * (projection S I).card := by
      rw [hm] at hbU
      exact_mod_cast hbU
    have hbV' : (A.card : ℝ) * (projection S (I ∪ V)).card ≤
        ((4 * 2 ^ m : ℕ) : ℝ) * H * maxRestrictedFan A I * (projection S I).card := by
      rw [hm] at hbV
      exact_mod_cast hbV
    have hempty (J : Finset ι) (hJ : Finset.univ \ J = ∅)
        (hbal : (A.card : ℝ) * (projection S J).card ≤
          ((4 * 2 ^ m : ℕ) : ℝ) * H * maxRestrictedFan A I * (projection S I).card) :
        fanLogBound m A.card H (projection S I).card ≤ Real.log (maxRestrictedFan A I) := by
      have he := projection_card_eq_card_of_covers S J (covers_of_remaining_empty hJ)
      rw [he] at hbal
      apply fanLogBound_le_of_empty_split hm2 hn hnH hM (hPpos I) hPn
      apply (mul_le_mul_of_nonneg_left (show (A.card : ℝ) ≤ S.card by exact_mod_cast Finset.card_le_card hAS)
        hn.le).trans hbal
    by_cases hpzero : U.card = 0
    · exact hempty (I ∪ V) (hremV.trans (Finset.card_eq_zero.mp hpzero)) hbV'
    by_cases hszero : V.card = 0
    · exact hempty (I ∪ U) (hremU.trans (Finset.card_eq_zero.mp hszero)) hbU'
    have hp : 0 < U.card := Nat.pos_of_ne_zero hpzero
    have hs : 0 < V.card := Nat.pos_of_ne_zero hszero
    have hpLt : U.card < m := by omega
    have hsLt : V.card < m := by omega
    have hhalf (k : ℕ) (hk : 0 < k) (hkm : k < m) (J : Finset ι)
        (hJ : (Finset.univ \ J).card = k) (B : Finset (ι → ℝ)) (hBA : B ⊆ A)
        (hlarge : A.card ≤ 2 * B.card) :
        Real.exp (fanLogBound k ((A.card : ℝ) / 2) H (projection S J).card) ≤ maxRestrictedFan B J := by
      have hB : B.Nonempty := Finset.card_pos.mp (by have := hA.card_pos; omega)
      have hb := ih k hkm J hJ hk B (hBA.trans hAS) hB
      have hbsize : (A.card : ℝ) / 2 ≤ B.card := by
        have he : (A.card : ℝ) ≤ 2 * B.card := by exact_mod_cast hlarge
        linarith
      have hmono := fanLogBound_mono (H := (H : ℝ)) (P := ((projection S J).card : ℝ)) hk
        (div_pos hn (by norm_num)) hbsize
      have hmB : (0 : ℝ) < maxRestrictedFan B J := by
        have h := one_le_maxRestrictedFan hB J
        exact_mod_cast (show 0 < maxRestrictedFan B J by omega)
      exact (Real.le_log_iff_exp_le hmB).mp (hmono.trans hb)
    have hprod := aggregate_pruning hA (I ∪ U) (I ∪ V) (partition_cover I U) I
      Finset.subset_union_left Finset.subset_union_left
      (Real.exp (fanLogBound U.card ((A.card : ℝ) / 2) H (projection S (I ∪ V)).card))
      (Real.exp (fanLogBound V.card ((A.card : ℝ) / 2) H (projection S (I ∪ U)).card))
      (Real.exp_pos _).le
      (hhalf U.card hp hpLt (I ∪ V) (congrArg Finset.card hremV))
      (hhalf V.card hs hsLt (I ∪ U) (congrArg Finset.card hremU))
    have hresult := fanLogBound_split hp hs hn hnH hM (hPpos I) hPn
      (hPpos (I ∪ U)) (hPpos (I ∪ V))
      (by simpa only [hdim] using hbU') (by simpa only [hdim] using hbV') hprod
    simpa only [hdim] using hresult

omit [Fintype ι] in
theorem projection_empty_card {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    (projection S ∅).card = 1 := by
  classical
  obtain ⟨a, ha⟩ := hS
  apply Finset.card_eq_one.mpr
  refine ⟨project ∅ a, ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_singleton.mpr
    funext i
    exact False.elim (Finset.notMem_empty i.val i.property)
  · intro hz
    have he := Finset.mem_singleton.mp hz
    rw [he]
    exact Finset.mem_image_of_mem _ ha

/-- A direct lower bound for the largest anchored fan, with all constants
specified, stated logarithmically to support the PFR transfer. -/
theorem uniform_log_bound {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (hd : 0 < Fintype.card ι) (H : ℕ)
    (hH : ∀ J, (projection S J).card * maxFiber S (project J) ≤ H) :
    -8 * (Fintype.card ι : ℝ) * Real.log 2 +
      regularityCost (Fintype.card ι) * (Real.log S.card - Real.log H) +
      uniformExponent (Fintype.card ι) * Real.log S.card ≤ Real.log (maxFan S) := by
  have h := aggregate_log_bound hS H hH (Fintype.card ι) ∅
    (by simp) hd S (Finset.Subset.refl S) hS
  simpa only [fanLogBound, projection_empty_card hS, Nat.cast_one, Real.log_one, sub_zero,
    maxRestrictedFan_empty] using h

theorem uniform_log_bound_differences {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (hd : 0 < Fintype.card ι) :
    -8 * (Fintype.card ι : ℝ) * Real.log 2 +
      regularityCost (Fintype.card ι) * (Real.log S.card - Real.log (differences S).card) +
      uniformExponent (Fintype.card ι) * Real.log S.card ≤ Real.log (maxFan S) :=
  uniform_log_bound hS hd (differences S).card (projection_mul_maxFiber_le_differences S)

end
end Erdos539Geometry
