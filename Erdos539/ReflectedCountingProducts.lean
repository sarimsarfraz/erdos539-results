/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedDefectComparison
import Erdos539.ProductNorm

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

theorem product_sumset (S : Finset G) (T : Finset H) :
    (S ×ˢ T) + (S ×ˢ T) = (S + S) ×ˢ (T + T) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_add, Finset.mem_product, Prod.exists, Prod.mk_add_mk, Prod.mk.injEq]
  aesop

theorem reflectedSupport_product (S : Finset G) (T : Finset H) (w : G × H) :
    reflectedSupport (S ×ˢ T) w = reflectedSupport S w.1 ×ˢ reflectedSupport T w.2 := by
  ext ⟨x, y⟩
  simp [reflectedSupport, and_assoc, and_left_comm]

theorem countingEnergy_product (S : Finset G) (T : Finset H) :
    countingEnergy (S ×ˢ T) = countingEnergy S * countingEnergy T := by
  simpa only [one_mul] using weightedEnergy_tensor S T (fun _ ↦ 1) (fun _ ↦ 1)

def countingDefect (S : Finset G) : ℝ := Real.log ((S.card : ℝ) ^ 3 / countingEnergy S)

theorem countingDefect_product {S : Finset G} {T : Finset H} (hS : S.Nonempty) (hT : T.Nonempty) :
    countingDefect (S ×ˢ T) = countingDefect S + countingDefect T := by
  unfold countingDefect
  rw [Finset.card_product, Nat.cast_mul, countingEnergy_product, mul_pow, mul_div_mul_comm,
    Real.log_mul]
  · exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast hS.card_pos.ne')) (countingEnergy_pos hS).ne'
  · exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast hT.card_pos.ne')) (countingEnergy_pos hT).ne'

theorem countingReflectionWeight_product (S : Finset G) (T : Finset H) (w : G × H) :
    countingReflectionWeight (S ×ˢ T) w = countingReflectionWeight S w.1 * countingReflectionWeight T w.2 := by
  simp only [countingReflectionWeight, reflectedSupport_product, Finset.card_product,
    Nat.cast_mul, countingEnergy_product, mul_pow, mul_div_mul_comm]

/-- Ordinary reflected defect, including its actual sampling weights,
adds exactly on Cartesian products. -/
theorem reflectedMeanCountingDefect_product {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    reflectedMeanCountingDefect (S ×ˢ T) = reflectedMeanCountingDefect S + reflectedMeanCountingDefect T := by
  unfold reflectedMeanCountingDefect
  rw [product_sumset, Finset.sum_product]
  change (∑ w ∈ S + S, ∑ z ∈ T + T,
    countingReflectionWeight (S ×ˢ T) (w, z) * countingDefect (reflectedSupport (S ×ˢ T) (w, z))) = _
  have he : (∑ w ∈ S + S, ∑ z ∈ T + T,
      countingReflectionWeight (S ×ˢ T) (w, z) * countingDefect (reflectedSupport (S ×ˢ T) (w, z))) =
      ∑ w ∈ S + S, ∑ z ∈ T + T,
        ((countingReflectionWeight S w * countingDefect (reflectedSupport S w)) * countingReflectionWeight T z +
          countingReflectionWeight S w * (countingReflectionWeight T z * countingDefect (reflectedSupport T z))) := by
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro z hz
    rw [countingReflectionWeight_product, reflectedSupport_product,
      countingDefect_product (reflectedSupport_nonempty_of_mem_add hw) (reflectedSupport_nonempty_of_mem_add hz)]
    dsimp only
    ring
  rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, countingReflectionWeight_sum hT,
    mul_one, ← Finset.sum_mul, countingReflectionWeight_sum hS, one_mul]
  rfl

end
end Erdos539Geometry
