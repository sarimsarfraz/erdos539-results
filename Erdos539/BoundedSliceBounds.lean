/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SliceBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- Transfer a lower-dimensional fan bound through a largest coordinate slice. -/
theorem bounded_restricted_log_bound_of_slice_bound {A S : Finset (ι → ℝ)}
    (hAS : A ⊆ S) (hA : A.Nonempty) {N : ℕ} (hSN : S.card ≤ N) (I J : Finset ι)
    (hcover : ∀ i, i ∈ I ∨ i ∈ J) (e c : ℝ) (he : 0 ≤ e)
    (hbound : ∀ F : Finset (J → ℝ), F.Nonempty → F.card ≤ N → e * Real.log F.card - c ≤ Real.log (maxFan F)) :
    e * (Real.log A.card - Real.log (projection S I).card) - c ≤ Real.log (maxRestrictedFan A I) := by
  obtain ⟨a, ha, havg⟩ := exists_large_slice hAS hA I
  have hs : (slice A I a).Nonempty := ⟨a, mem_slice.mpr ⟨ha, rfl⟩⟩
  have hF : (projection (slice A I a) J).Nonempty := hs.image _
  have hn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hP : (0 : ℝ) < (projection S I).card := by exact_mod_cast ((hA.mono hAS).image (project I)).card_pos
  have hslice : (0 : ℝ) < (slice A I a).card := by exact_mod_cast hs.card_pos
  have havg' : (A.card : ℝ) ≤ (projection S I).card * ((slice A I a).card : ℝ) := by exact_mod_cast havg
  have hl := Real.log_le_log hn havg'
  rw [Real.log_mul hP.ne' hslice.ne'] at hl
  have hcard : (projection (slice A I a) J).card ≤ N := by
    rw [projection_slice_card A I J hcover a]
    exact (Finset.card_le_card (slice_subset A I a)).trans ((Finset.card_le_card hAS).trans hSN)
  have hf := hbound _ hF hcard
  rw [projection_slice_card A I J hcover a] at hf
  have hM : (0 : ℝ) < maxFan (projection (slice A I a) J) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
  have hmono := Real.log_le_log hM (show (maxFan (projection (slice A I a) J) : ℝ) ≤ maxRestrictedFan A I by
    exact_mod_cast maxFan_projection_slice_le A I J a)
  have he' := mul_le_mul_of_nonneg_left (show Real.log A.card - Real.log (projection S I).card ≤
    Real.log (slice A I a).card by linarith) he
  linarith

/-- General one-sided pruning, preserving the original anchor throughout. -/
theorem bounded_one_sided_log_pruning {A : Finset (ι → ℝ)} (hA : A.Nonempty) {N : ℕ} (hAN : A.card ≤ N)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → F.card ≤ N → a * Real.log F.card - c ≤ Real.log (maxFan F))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → F.card ≤ N → b * Real.log F.card - d ≤ Real.log (maxFan F)) :
    a * (Real.log A.card - Real.log 2 - Real.log (projection A J).card) +
      b * (Real.log A.card - Real.log 2 - Real.log (projection A I).card) - c - d ≤ Real.log (maxFan A) := by
  classical
  have hhalf (K L : Finset ι) (hcov : ∀ i, i ∈ K ∨ i ∈ L) (e loss : ℝ) (he : 0 ≤ e)
      (hbound : ∀ F : Finset (L → ℝ), F.Nonempty → F.card ≤ N → e * Real.log F.card - loss ≤ Real.log (maxFan F))
      (B : Finset (ι → ℝ)) (hBA : B ⊆ A) (hlarge : A.card ≤ 2 * B.card) :
      Real.exp (e * (Real.log A.card - Real.log 2 - Real.log (projection A K).card) - loss) ≤
        maxRestrictedFan B K := by
    have hB : B.Nonempty := Finset.card_pos.mp (by have := hA.card_pos; omega)
    have hbase := bounded_restricted_log_bound_of_slice_bound hBA hB hAN K L hcov e loss he hbound
    have hn : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hbn : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    have hl := Real.log_le_log hn (show (A.card : ℝ) ≤ 2 * B.card by exact_mod_cast hlarge)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hbn.ne'] at hl
    have hmul := mul_le_mul_of_nonneg_left (show Real.log A.card - Real.log 2 ≤ Real.log B.card by linarith) he
    have hM : (0 : ℝ) < maxRestrictedFan B K := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxRestrictedFan hB K))
    apply (Real.le_log_iff_exp_le hM).mp
    linarith
  have hp := aggregate_pruning hA I J hcover ∅ (Finset.empty_subset _) (Finset.empty_subset _)
    (Real.exp (a * (Real.log A.card - Real.log 2 - Real.log (projection A J).card) - c))
    (Real.exp (b * (Real.log A.card - Real.log 2 - Real.log (projection A I).card) - d))
    (Real.exp_pos _).le
    (hhalf J I (fun i ↦ (hcover i).symm) a c ha hI)
    (hhalf I J hcover b d hb hJ)
  rw [maxRestrictedFan_empty, ← Real.exp_add] at hp
  have hM : (0 : ℝ) < maxFan A := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hA))
  have hl := (Real.le_log_iff_exp_le hM).mpr hp
  linarith

end
end Erdos539Geometry
