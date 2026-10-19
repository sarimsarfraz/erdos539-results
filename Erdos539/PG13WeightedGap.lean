/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13ProjectionDefect
import Erdos539.PG13WeightedCoefficient
import Erdos539.StationaryFanCapacity

namespace Erdos539Geometry
noncomputable section
open scoped Classical

def pg13DefectConstant : ℝ := 2 * Real.log 13 + 7 * Real.log 2
def pg13GapCoefficient : ℝ := 5400 / 4226183

def pg13FanCapacity (T : ℕ) : ℝ :=
  stationaryFanCapacity (integerRealSet (pg13Union T)) (uniformReference (integerRealSet (pg13Union T)))

theorem pg13DefectConstant_nonneg : 0 ≤ pg13DefectConstant := by
  unfold pg13DefectConstant
  positivity

theorem pg13_coefficient_bounds (I : Finset (Fin 13)) :
    0 ≤ (stationaryCutExponent I.card : ℝ) ∧ (stationaryCutExponent I.card : ℝ) ≤ 2 / 3 := by
  have hi : I.card < 14 := by have := Finset.card_le_univ I; norm_num at this; omega
  have h := pg13_cut_exponent_bounds ⟨I.card, hi⟩
  change (0 : ℚ) ≤ stationaryCutExponent I.card ∧ stationaryCutExponent I.card ≤ 2 / 3 at h
  constructor
  · exact Rat.cast_nonneg.mpr h.1
  · have hh : (stationaryCutExponent I.card : ℝ) ≤ ((2 / 3 : ℚ) : ℝ) := Rat.cast_le.mpr h.2
    norm_num at hh ⊢
    exact hh

theorem pg13FanCapacity_le_log {T : ℕ} (hT : 0 < T) :
    pg13FanCapacity T ≤ Real.log (maxFan (integerRealSet (pg13Union T)) : ℝ) := by
  have hS := integerRealSet_nonempty (pg13Union_nonempty hT)
  exact stationaryFanCapacity_le_log_maxFan _ _ (fun x ↦ (uniformReference_pos hS x).le)
    (uniformReference_sum hS)

theorem pg13ProjectionProfile_eq (T : ℕ) (I : Finset (Fin 13)) :
    pg13ProjectionProfile T I = pg13ProjectionEntropy T I - pg13ProjectionDefect T I :=
  stationaryEnergyProfile_eq_entropy_sub_defect _ _

/-- The dimension-weighted entropy gap for every nonempty proper cut,
with the actual stationary forward-fan capacity. -/
theorem pg13_weighted_entropy_gap {T : ℕ} (hT : 2 ≤ T) (I : Finset (Fin 13))
    (hI : I.Nonempty) (hJ : Iᶜ.Nonempty) :
    let a : ℝ := stationaryCutExponent I.card
    let b : ℝ := stationaryCutExponent Iᶜ.card
    pg13GapCoefficient * Real.log (T : ℝ) - (a + b) * Real.log 11 ≤
      a * pg13ProjectionEntropy T Iᶜ + b * pg13ProjectionEntropy T I -
        (a + b) * pg13FanCapacity T := by
  dsimp only
  have hp : 0 < T := by omega
  have ha := (pg13_coefficient_bounds I).1
  have hb := (pg13_coefficient_bounds Iᶜ).1
  have hw : pg13GapCoefficient ≤
      ((stationaryCutExponent I.card : ℝ) * pg13VisibleWeight Iᶜ +
        (stationaryCutExponent Iᶜ.card : ℝ) * pg13VisibleWeight I) / 13 -
          4 * ((stationaryCutExponent I.card : ℝ) + (stationaryCutExponent Iᶜ.card : ℝ)) := by
    unfold pg13GapCoefficient
    have hh := (Rat.cast_le (K := ℝ)).mpr (pg13_weighted_coefficient I hI hJ)
    push_cast at hh
    exact hh
  have hlog : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hcoeff := mul_le_mul_of_nonneg_right hw hlog
  have h₁ := mul_le_mul_of_nonneg_left (pg13Union_projection_entropy hp Iᶜ) ha
  have h₂ := mul_le_mul_of_nonneg_left (pg13Union_projection_entropy hp I) hb
  have h₃ := mul_le_mul_of_nonneg_left
    ((pg13FanCapacity_le_log hp).trans (pg13Union_log_maxFan_le hT)) (add_nonneg ha hb)
  change _ ≤ (stationaryCutExponent I.card : ℝ) * pg13ProjectionEntropy T Iᶜ at h₁
  change _ ≤ (stationaryCutExponent Iᶜ.card : ℝ) * pg13ProjectionEntropy T I at h₂
  nlinarith

/-- Energy adjustment leaves a positive logarithmic gap, despite bounded
stationary defect of the parent and every projected law. -/
theorem pg13_weighted_profile_gap {T : ℕ} (hT : 2 ≤ T) (I : Finset (Fin 13))
    (hI : I.Nonempty) (hJ : Iᶜ.Nonempty) :
    let a : ℝ := stationaryCutExponent I.card
    let b : ℝ := stationaryCutExponent Iᶜ.card
    pg13GapCoefficient * Real.log (T : ℝ) - (a + b) * (pg13DefectConstant + Real.log 11) ≤
      a * pg13ProjectionProfile T Iᶜ + b * pg13ProjectionProfile T I -
        (a + b) * pg13FanCapacity T := by
  dsimp only
  have hp : 0 < T := by omega
  have h := pg13_weighted_entropy_gap hT I hI hJ
  dsimp only at h
  have h₁ := mul_le_mul_of_nonneg_left (pg13Union_projection_defect hp Iᶜ)
    (pg13_coefficient_bounds I).1
  have h₂ := mul_le_mul_of_nonneg_left (pg13Union_projection_defect hp I)
    (pg13_coefficient_bounds Iᶜ).1
  rw [pg13ProjectionProfile_eq, pg13ProjectionProfile_eq]
  unfold pg13DefectConstant
  nlinarith

/-- Any fixed nonnegative coefficient multiplying projected stationary
defects still leaves the same positive logarithmic leading term. -/
theorem pg13_weighted_entropy_penalty {T : ℕ} (hT : 2 ≤ T) (I : Finset (Fin 13))
    (hI : I.Nonempty) (hJ : Iᶜ.Nonempty) {A : ℝ} (hA : 0 ≤ A) :
    let a : ℝ := stationaryCutExponent I.card
    let b : ℝ := stationaryCutExponent Iᶜ.card
    pg13GapCoefficient * Real.log (T : ℝ) - (a + b) * Real.log 11 - 2 * A * pg13DefectConstant ≤
      a * pg13ProjectionEntropy T Iᶜ + b * pg13ProjectionEntropy T I -
        (a + b) * pg13FanCapacity T - A * (pg13ProjectionDefect T I + pg13ProjectionDefect T Iᶜ) := by
  dsimp only
  have hp : 0 < T := by omega
  have h := pg13_weighted_entropy_gap hT I hI hJ
  dsimp only at h
  have hδ := mul_le_mul_of_nonneg_left
    (add_le_add (pg13Union_projection_defect hp I) (pg13Union_projection_defect hp Iᶜ)) hA
  unfold pg13DefectConstant
  linarith

end
end Erdos539Geometry
