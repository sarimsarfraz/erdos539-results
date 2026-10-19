/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FullDifferencePruning
import Erdos539.TwoSidedLogPruning

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- Full positive-difference pruning with a two-sided bound on the first block. -/
theorem full_difference_log_pruning {A : Finset (ι → ℝ)} (hA : A.Nonempty)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → a * Real.log F.card - c ≤ Real.log (maxTwoFan F))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → b * Real.log F.card - d ≤ Real.log (posDiff F).card) :
    a * (Real.log A.card - Real.log 2 - Real.log (projection A J).card) +
      b * (Real.log A.card - Real.log 4 - Real.log (projection A I).card) - c - d ≤
        Real.log (posDiff A).card := by
  have hfirst (B : Finset (ι → ℝ)) (hBA : B ⊆ A) (hlarge : A.card ≤ 2 * B.card) :
      Real.exp (a * (Real.log A.card - Real.log 2 - Real.log (projection A J).card) - c) ≤
        maxTwoRestrictedFan B J := by
    have hB : B.Nonempty := Finset.card_pos.mp (by have := hA.card_pos; omega)
    have hbase := restricted_two_log_bound_of_slice_bound hBA hB J I
      (fun i ↦ (hcover i).symm) a c ha hI
    have hM : (0 : ℝ) < maxTwoRestrictedFan B J := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxTwoRestrictedFan hB J))
    exact exp_threshold_of_log_bound hA.card_pos (by decide : 0 < 2) hlarge a c _ _ ha hM hbase
  have hsecond (B : Finset (ι → ℝ)) (hBA : B ⊆ A) (hlarge : A.card ≤ 4 * B.card) :
      Real.exp (b * (Real.log A.card - Real.log 4 - Real.log (projection A I).card) - d) ≤
        maxRestrictedPosDiff B I := by
    have hB : B.Nonempty := Finset.card_pos.mp (by have := hA.card_pos; omega)
    have hbase := restricted_posDiff_log_bound_of_slice_bound hBA hB I J hcover b d hb hJ
    have hM : (0 : ℝ) < maxRestrictedPosDiff B I := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxRestrictedPosDiff hB I))
    exact exp_threshold_of_log_bound hA.card_pos (by decide : 0 < 4) hlarge b d _ _ hb hM hbase
  have hp := aggregate_full_difference_pruning hA I J hcover
    (Real.exp (a * (Real.log A.card - Real.log 2 - Real.log (projection A J).card) - c))
    (Real.exp (b * (Real.log A.card - Real.log 4 - Real.log (projection A I).card) - d))
    (Real.exp_pos _).le hfirst hsecond
  rw [← Real.exp_add] at hp
  have hq : 0 < (posDiff A).card :=
    lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hA)) (maxFan_le_card_posDiff _)
  have hM : (0 : ℝ) < (posDiff A).card := by exact_mod_cast hq
  have hl := (Real.le_log_iff_exp_le hM).mpr hp
  linarith

end
end Erdos539Geometry
