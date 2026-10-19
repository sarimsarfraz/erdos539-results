/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.AggregatePruning
import Erdos539.RestrictedBase
import Erdos539.LogPruning

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

theorem projection_singleton_card_le_maxFan (F : Finset (ι → ℝ)) (i : ι) :
    (projection F {i}).card ≤ maxFan F := by
  classical
  have h : (projection F {i}).card ≤ (F.image (fun x ↦ x i)).card := by
    apply Finset.card_le_card_of_injOn (fun v : ({i} : Finset ι) → ℝ ↦ v ⟨i, by simp⟩)
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image_of_mem _ hx
    · intro v _ w _ he
      funext k
      have hk : k = ⟨i, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp k.property)
      rw [hk]
      exact he
  exact h.trans (coordinate_card_le_maxFan F i)

theorem one_free_half_bound {A : Finset (ι → ℝ)} (hA : A.Nonempty)
    (J : Finset ι) (i : ι) (hcover : ∀ j, j ∈ J ∨ j = i)
    {B : Finset (ι → ℝ)} (hBA : B ⊆ A) (hlarge : A.card ≤ 2 * B.card) :
    (A.card : ℝ) / (2 * (projection A J).card) ≤ maxRestrictedFan B J := by
  have hP : (0 : ℝ) < (projection A J).card := by
    exact_mod_cast Finset.card_pos.mpr (hA.image (project J))
  apply (div_le_iff₀ (mul_pos (by norm_num) hP)).mpr
  have hB : (B.card : ℝ) ≤ (projection A J).card * maxRestrictedFan B J := by
    exact_mod_cast card_le_projection_mul_restrictedFan_one_free hBA J i hcover
  have hn : (A.card : ℝ) ≤ 2 * B.card := by exact_mod_cast hlarge
  nlinarith

/-- The planar fan inequality, proved by aggregate pruning and the two
coordinate projection bounds. This includes the degenerate one-coordinate case. -/
theorem planar_card_sq_le_four_maxFan_cube_of_cover
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) (i j : ι)
    (hcover : ∀ k, k = i ∨ k = j) :
    (F.card : ℝ) ^ 2 ≤ 4 * (maxFan F : ℝ) ^ 3 := by
  classical
  have hcov : ∀ k, k ∈ ({i} : Finset ι) ∨ k ∈ ({j} : Finset ι) := by
    intro k
    simpa only [Finset.mem_singleton] using hcover k
  have hfirst : ∀ k, k ∈ ({j} : Finset ι) ∨ k = i := by
    intro k
    simpa only [Finset.mem_singleton, or_comm] using hcover k
  have hsecond : ∀ k, k ∈ ({i} : Finset ι) ∨ k = j := by
    intro k
    simpa only [Finset.mem_singleton] using hcover k
  have hPi : (0 : ℝ) < (projection F {i}).card := by exact_mod_cast (hF.image (project {i})).card_pos
  have hPj : (0 : ℝ) < (projection F {j}).card := by exact_mod_cast (hF.image (project {j})).card_pos
  have hprune := aggregate_pruning hF {i} {j} hcov ∅ (Finset.empty_subset _) (Finset.empty_subset _)
    ((F.card : ℝ) / (2 * (projection F {j}).card))
    ((F.card : ℝ) / (2 * (projection F {i}).card)) (by positivity)
    (fun B hBF hlarge ↦ one_free_half_bound hF {j} i hfirst hBF hlarge)
    (fun B hBF hlarge ↦ one_free_half_bound hF {i} j hsecond hBF hlarge)
  rw [maxRestrictedFan_empty, div_mul_div_comm] at hprune
  have hraw := (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hPj) (mul_pos (by norm_num) hPi))).mp hprune
  have hi : ((projection F {i}).card : ℝ) ≤ maxFan F := by exact_mod_cast projection_singleton_card_le_maxFan F i
  have hj : ((projection F {j}).card : ℝ) ≤ maxFan F := by exact_mod_cast projection_singleton_card_le_maxFan F j
  have hmul := mul_le_mul hi hj hPj.le (show (0 : ℝ) ≤ maxFan F by positivity)
  calc
    (F.card : ℝ) ^ 2 ≤ (4 * maxFan F) *
        ((projection F {i}).card * ((projection F {j}).card : ℝ)) := by nlinarith
    _ ≤ (4 * maxFan F) * ((maxFan F : ℝ) * maxFan F) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by ring

theorem planar_card_sq_le_four_maxFan_cube [Fintype ι] (hd : Fintype.card ι = 2)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ 2 ≤ 4 * (maxFan F : ℝ) ^ 3 := by
  classical
  obtain ⟨i, j, _hne, hij⟩ := Finset.card_eq_two.mp (show (Finset.univ : Finset ι).card = 2 by simpa using hd)
  apply planar_card_sq_le_four_maxFan_cube_of_cover hF i j
  intro k
  have hk : k ∈ ({i, j} : Finset ι) := hij ▸ Finset.mem_univ k
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hk

theorem planar_log_fan_bound [Fintype ι] (hd : Fintype.card ι = 2)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (2 / 3 : ℝ) * Real.log F.card - (2 / 3 : ℝ) * Real.log 2 ≤ Real.log (maxFan F) := by
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hM : (0 : ℝ) < maxFan F := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
  have h := Real.log_le_log (sq_pos_of_pos hn) (planar_card_sq_le_four_maxFan_cube hd hF)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_pos hM 3).ne', Real.log_pow, Real.log_pow] at h
  have h4 := Real.log_pow (2 : ℝ) 2
  norm_num at h4 h
  linarith

end
end Erdos539Geometry
