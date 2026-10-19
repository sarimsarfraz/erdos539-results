/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteBlockEntropy
import Erdos539.FiniteFractionalCover

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem finite_codimension_cover {κ : Type*} [Fintype κ] (H : Finset κ → ℝ)
    (h0 : H ∅ = 0) (hmono : Monotone H)
    (hinc : ∀ {I J : Finset κ}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    (hk : 2 ≤ Fintype.card κ) :
    ((Fintype.card κ : ℝ) - 1) * H Finset.univ ≤ ∑ i, H (Finset.univ.erase i) := by
  have hkreal : (2 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hk
  have hpos : 0 < (Fintype.card κ : ℝ) - 1 := by linarith
  let c : ℝ := 1 / ((Fintype.card κ : ℝ) - 1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcover (i : κ) : 1 ≤ ∑ k : κ, if i ∈ Finset.univ.erase k then c else 0 := by
    have he : (∑ k : κ, if i ∈ Finset.univ.erase k then c else 0) =
        ∑ k ∈ Finset.univ.erase i, c := by
      have hset : Finset.univ.erase i =
          Finset.univ.filter (fun k : κ ↦ i ∈ Finset.univ.erase k) := by
        ext k
        simp [eq_comm]
      conv_rhs => rw [hset, Finset.sum_filter]
    rw [he]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Nat.cast_sub (show 1 ≤ Fintype.card κ by omega), Nat.cast_one]
    dsimp [c]
    rw [mul_one_div_cancel hpos.ne']
  have h := finite_fractional_cover H h0 hmono (fun {_ _} h i _ ↦ hinc h i)
    (fun i : κ ↦ Finset.univ.erase i) (fun _ ↦ c) (fun _ ↦ hc)
    Finset.univ (fun i _ ↦ hcover i)
  simp only [Finset.inter_univ, ← Finset.mul_sum] at h
  have hm := mul_le_mul_of_nonneg_left h hpos.le
  dsimp [c] at hm
  simpa only [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] using hm

theorem block_increment_antitone {ι κ : Type*} (H : Finset ι → ℝ)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    (V : κ → Finset ι) {I J : Finset κ} (hIJ : I ⊆ J) (i : κ) :
    H ((insert i J).biUnion V) - H (J.biUnion V) ≤
      H ((insert i I).biUnion V) - H (I.biUnion V) := by
  have h := finite_union_increment_antitone H hinc
    (Finset.biUnion_subset_biUnion_of_subset_left V hIJ) (V i)
  simpa only [Finset.biUnion_insert, Finset.union_comm] using h

/-- Conditional subadditivity for arbitrary finite blocks, including overlaps. -/
theorem block_conditional_subadditivity {ι κ : Type*} (H : Finset ι → ℝ)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    (U : κ → Finset ι) (C : Finset ι) (A : Finset κ) :
    H (C ∪ A.biUnion U) - H C ≤ ∑ i ∈ A, (H (C ∪ U i) - H C) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have h := finite_union_increment_antitone H hinc
      (Finset.subset_union_left : C ⊆ C ∪ A.biUnion U) (U i)
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have he : (C ∪ A.biUnion U) ∪ U i = C ∪ (U i ∪ A.biUnion U) := by
      ext x
      simp only [Finset.mem_union]
      tauto
    rw [he] at h
    linarith

def blockUnion {ι κ : Type*} [Fintype κ] (V : κ → Finset ι) : Finset ι := Finset.univ.biUnion V
def blockOthers {ι κ : Type*} [Fintype κ] (V : κ → Finset ι) (i : κ) : Finset ι :=
  (Finset.univ.erase i).biUnion V

theorem block_Han {ι κ : Type*} [Fintype κ] (H : Finset ι → ℝ)
    (h0 : H ∅ = 0) (hmono : Monotone H)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    (V : κ → Finset ι) (hk : 2 ≤ Fintype.card κ) :
    ((Fintype.card κ : ℝ) - 1) * H (blockUnion V) ≤ ∑ i, H (blockOthers V i) := by
  exact finite_codimension_cover (fun A ↦ H (A.biUnion V)) (by simpa using h0)
    (fun _ _ h ↦ hmono (Finset.biUnion_subset_biUnion_of_subset_left V h))
    (fun {_ _} h i ↦ block_increment_antitone H hinc V h i) hk

end
end Erdos539Geometry
