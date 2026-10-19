/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.TwoSidedPruning
import Erdos539.SignedReflection
import Erdos539.SignedSliceBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- Convert a logarithmic lower bound on a large subset to a uniform
exponential threshold for pruning. -/
theorem exp_threshold_of_log_bound {n m k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hlarge : n ≤ k * m) (e c P M : ℝ) (he : 0 ≤ e) (hM : 0 < M)
    (hbound : e * (Real.log m - P) - c ≤ Real.log M) :
    Real.exp (e * (Real.log n - Real.log k - P) - c) ≤ M := by
  have hm : 0 < m := by nlinarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl := Real.log_le_log hn' (show (n : ℝ) ≤ k * (m : ℝ) by exact_mod_cast hlarge)
  rw [Real.log_mul hk'.ne' hm'.ne'] at hl
  have hmul := mul_le_mul_of_nonneg_left (show Real.log n - Real.log k ≤ Real.log m by linarith) he
  apply (Real.le_log_iff_exp_le hM).mp
  linarith

/-- The two-sided anchored pruning lemma in logarithmic form, with the
quarter-density loss confined to the block requiring both directions. -/
theorem two_sided_log_pruning {A : Finset (ι → ℝ)} (hA : A.Nonempty)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → a * Real.log F.card - c ≤ Real.log (maxFan F))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → b * Real.log F.card - d ≤ Real.log (maxTwoFan F)) :
    a * (Real.log A.card - Real.log 4 - Real.log (projection A J).card) +
      b * (Real.log A.card - Real.log 2 - Real.log (projection A I).card) - c - d ≤
        Real.log (maxTwoFan A) := by
  have hfirst (sign : Bool) (B : Finset (ι → ℝ)) (hBA : B ⊆ A) (hlarge : A.card ≤ 4 * B.card) :
      Real.exp (a * (Real.log A.card - Real.log 4 - Real.log (projection A J).card) - c) ≤
        maxSignedRestrictedFan sign B J := by
    have hB : B.Nonempty := Finset.card_pos.mp (by have := hA.card_pos; omega)
    have hbase := restricted_signed_log_bound_of_slice_bound sign hBA hB J I
      (fun i ↦ (hcover i).symm) a c ha hI
    have hM : (0 : ℝ) < maxSignedRestrictedFan sign B J := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxSignedRestrictedFan sign hB J))
    exact exp_threshold_of_log_bound hA.card_pos (by decide : 0 < 4) hlarge a c _ _ ha hM hbase
  have hsecond (B : Finset (ι → ℝ)) (hBA : B ⊆ A) (hlarge : A.card ≤ 2 * B.card) :
      Real.exp (b * (Real.log A.card - Real.log 2 - Real.log (projection A I).card) - d) ≤
        maxTwoRestrictedFan B I := by
    have hB : B.Nonempty := Finset.card_pos.mp (by have := hA.card_pos; omega)
    have hbase := restricted_two_log_bound_of_slice_bound hBA hB I J hcover b d hb hJ
    have hM : (0 : ℝ) < maxTwoRestrictedFan B I := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxTwoRestrictedFan hB I))
    exact exp_threshold_of_log_bound hA.card_pos (by decide : 0 < 2) hlarge b d _ _ hb hM hbase
  have hp := aggregate_two_sided_pruning hA I J hcover ∅ (Finset.empty_subset _) (Finset.empty_subset _)
    (Real.exp (a * (Real.log A.card - Real.log 4 - Real.log (projection A J).card) - c))
    (Real.exp (b * (Real.log A.card - Real.log 2 - Real.log (projection A I).card) - d))
    (Real.exp_pos _).le hfirst hsecond
  rw [← Real.exp_add] at hp
  have hM : (0 : ℝ) < maxTwoFan A := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxTwoRestrictedFan hA ∅))
  have hl := (Real.le_log_iff_exp_le hM).mpr hp
  linarith

end
end Erdos539Geometry
